package info.kwarc.p

class Parser(file: File, input: String) {
  private var index = 0
  override def toString = input.substring(index)

  case class Error(msg: String) extends PError(msg)
  def fail(msg: String) = {
    throw Error(msg + "; found " + input.substring(index))
  }

  def addRef[A<:SyntaxFragment](sf: => A): A = {
    trim
    val from = index
    val a = sf
    a.loc = Location(file, from, index)
    a
  }

  // all input has been parsed
  def atEnd = {index == input.length}

  // next character to parse
  def next = input(index)


  // string s occurs at the current index in the input
  // if s is only letters, we additionally check that no id char follows
  def startsWith(s: String): Boolean = {
    val isKeyword = s.forall(_.isLetter)
    val b = index+s.length <= input.length && input.substring(index, index+s.length) == s
    if (b && isKeyword) (index+s.length == input.length || !Path.isIdChar(input(index+s.length)))
    else b
  }
  // test for some strings, and if found, skip and trim
  def startsWithS(s: String): Boolean = {
    val b = startsWith(s)
    if (b) skip(s)
    b
  }

  // parses all whitespace at the current position
  def trim = {while (!atEnd && next.isWhitespace) index += 1}

  // parses the string s and throws it away
  def skip(s: String) = {
    if (!startsWith(s)) fail("expected " + s)
    index += s.length
  }
  def skipT(s: String) = {skip(s); trim}

  // whitespace-separated list with brackets
  def parseBracketedList[A](parse: => A, begin: String, end: String): List[A] = {
    skip(begin)
    val as = parseList(parse, end, false)
    skip(end)
    as
  }
  // list with separator
  def parseList[A](parse: => A, sep: String, emptyIf: String): List[A] = {
    if (startsWith(emptyIf)) Nil
    else parseList(parse, sep, true)
  }
  // isSeparator = true:  a1 lookFor ... lookFor an |
  // isSeparator = false: a1 ... an | lookFor
  private def parseList[A](parse: => A, lookFor: String, isSeparator: Boolean): List[A] = {
    var as: List[A] = Nil
    var break = false
    while (!break) {
      trim
      as ::= parse
      trim
      if (startsWith(lookFor)) {
        if (isSeparator) skip(lookFor) // skip separator and parse next element
        else break = true // stop character found, break
      } else {
        if (isSeparator) break = true // separator needed, break
        else {} // whitespace is separator, parse next
      }
    }
    as.reverse
  }

  def parseName: String = {
    trim
    val begin = index
    while (!atEnd && next.isLetterOrDigit) index += 1
    input.substring(begin,index)
  }

  def parsePath: Path = addRef {
    val ns = parseList(parseName, ".", " ")
    Path(ns)
  }

  def parseDeclaration: Declaration = addRef {
    if (startsWith("class") || startsWith(("module"))) parseModule
    else if (startsWith("include") || startsWith("realize")) parseInclude
    else if (startsWith("type")) parseTypeDecl
    else if (next.isLetter) parseExprDecl
    else fail("declaration expected")
  }

  def parseDeclarations: List[Declaration] = {
    var decls: List[Declaration] = Nil
    var break = false
    while (!break) {
      trim
      if (atEnd || startsWith("}")) {break = true}
      else decls ::= parseDeclaration
    }
    decls.reverse
  }

  def parseModule: Module = {
    val closed = if (startsWithS("class")) true else {skipT("module"); false}
    val name = parseName
    trim
    skip("{")
    val decls = parseDeclarations
    trim
    skip("}")
    Module(name, closed, decls)
  }

  def parseInclude: Include = {
    implicit val ctx = Context.empty
    val rz = if (startsWithS("include")) false else {skip("realize"); true}
    val dom = parsePath
    trim
    val dfO = if (!rz && startsWithS("=")) {
      Some(parseExpression)
    } else {
      None
    }
    Include(dom, dfO, rz)
  }

  def parseExprDecl: ExprDecl = {
    val name = parseName
    trim
    val tp = if (startsWithS(":")) {
      parseType(Context.empty)
    } else null
    trim
    val vl = if (startsWithS("=")) {
      Some(parseExpression(Context.empty))
    } else None
    ExprDecl(name, tp, vl)
  }

  def parseTypeDecl: TypeDecl = {
    skipT("type")
    val name = parseName
    trim
    val (tp,df) = if (startsWithS("=")) {
      (null,Some(parseType(Context.empty)))
    } else if (startsWithS("<")) {
      (parseType(Context.empty), None)
    } else
      (null, None)
    TypeDecl(name, tp, df)
  }

  def parseVarDecl(mutable: Boolean)(implicit ctx: Context): VarDecl = {
    val n = parseName
    trim
    val tp = if (startsWithS(":")) {
      parseType
    } else null
    val vl = if (startsWithS("=")) {
      Some(parseExpression)
    } else None
    VarDecl(n,tp,vl,mutable)
  }

  def parseTheory(implicit ctx: Context): Theory = {
    trim
    val ps = parseList(parsePath, "+", "|")
    Theory(ps)
  }

  def parseExpressions(implicit ctx: Context) = {
    skip("(")
    val es = parseList(parseExpression, ",", ")")
    skip(")")
    es
  }

  def parseExpression(implicit ctx: Context): Expression = addRef {parseExpressionInner}
  // needed because addRef does not work with return-statements
  private def parseExpressionInner(implicit ctx: Context): Expression = {
    var seen: List[(Expression,InfixOperator)] = Nil
    while (true) {
      trim
      var exp = if (startsWithS(".")) {
        OpenRef(parsePath, None)
      } else if (startsWithS("{")) {
        var cs: List[Expression] = Nil
        var ctxL = ctx
        trim
        while (!startsWithS("}")) {
          val c = parseExpression(ctxL)
          cs ::= c
          c match {
            case vd: VarDecl => ctxL = ctxL.append(vd)
            case _ =>
          }
          trim
          if (startsWith(";")) skip(";")
        }
        Block(cs.reverse)
      } else if (startsWithS("var")) {
        trim
        parseVarDecl(true)
      } else if (startsWithS("val")) {
        trim
        parseVarDecl(false)
      } else if (startsWithS("while")) {
        val c = parseExpression
        val b = parseExpression
        While(c,b)
      } else if (startsWithS("for")) {
        val v = parseName
        trim
        skipT("in")
        val r = parseExpression
        val b = parseExpression(ctx.append(VarDecl(v,null)))
        For(v,r,b)
      } else if (startsWithS("if")) {
        val c = parseExpression
        val th = parseExpression
        trim
        val el = if (startsWithS("else")) {
          Some(parseExpression)
        } else None
        IfThenElse(c,th,el)
      } else if (Operator.prefixes.exists(o => startsWith(o.symbol))) {
        val o = Operator.prefixes.find(o => startsWith(o.symbol)).get
        skip(o.symbol)
        val e = parseExpression
        Application(BaseOperator(o,null),List(e))
      } else if (startsWithS("\"")) {
        val begin = index
        while (next != '"') index += 1
        val end = index
        skip("\"")
        StringValue(input.substring(begin,end))
        /*    } else if (startsWith("'")) {
        skip("'")
        val c = next
        skip(c.toString)
        skip("'")
        CharLiteral(c)
  */
      } else if (startsWithS("true")) {
        BoolValue(true)
      } else if (startsWithS("false")) {
        BoolValue(false)
      } else if (next.isDigit || next == '-') {
        val begin = index
        if (next == '-') skip("-")
        var seenDot = false
        while (!atEnd && (next.isDigit || (!seenDot && next == '.'))) {
          if (next == '.') seenDot = true
          index += 1
        }
        val s = input.substring(begin,index)
        //if (seenDot) FloatLiteral(s.toFloat) else
        IntValue(s.toInt)
      } else if (startsWith("(")) {
        // unit (), bracketed (e), or tuple (e,...,e)
        val es = parseExpressions
        trim
        if (startsWith("->")) {
          skip("->")
          val vds = es.map {
            case vd: VarDecl => vd
            case VarRef(n) => VarDecl(n, null)
            case ClosedRef(n) => VarDecl(n, null)
            case _ => fail("not variable declaration")
          }
          val c = Context(vds)
          val b = parseExpression(ctx.append(c))
          Lambda(c, b)
        } else es match {
          case Nil => UnitValue
          case List(e) => e
          case es => Tuple(es)
        }
      } else if (startsWithS("list")) {
        val es = parseExpressions
        ListValue(es)
      } else {
        //  symbol/variable reference
        val p = parsePath
        if (p.names.length == 1) {
          val n = p.names.head
          trim
          if (startsWith(":")) {
            // variable declaration
            skip(":")
            val tp = parseType
            VarDecl(n,tp,None,false)
          } else if (ctx.domain.contains(n)) {
            // reference to bound variable
            VarRef(n)
          } else
            ClosedRef(n)
        } else
          OpenRef(p, None)
      } // end exp =
      trim
      val strongPostops = List('.', '(')
      while (!atEnd && (strongPostops contains next)) {
        // TODO: clashes with path-separator
        if (startsWithS(".")) {
          val f = parseExpression
          exp = OwnedExpr(exp, f)
        } else if (startsWith("(")) {
          val es = parseExpressions
          exp = Application(exp,es)
        }
      }
      Operator.infixes.find(o => startsWith(o.symbol)) match {
        case None =>
          if (startsWithS("=")) {
            val df = parseExpression
            exp = Assign(exp,df)
          }
          return disambiguateInfixOperators(seen.reverse, exp)
        case Some(o) =>
          skip(o.symbol)
          seen ::= (exp,o)
      }
    } // end while
    null // impossible
  }

  // a shift-reduce parser of e1 o1 ... en on last
  def disambiguateInfixOperators(eos: List[(Expression,InfixOperator)], lastExp: Expression): Expression = {
    // invariant: eos last = shifted rest last
    var shifted: List[(Expression, InfixOperator)] = Nil
    var rest = eos
    var last = lastExp
    // shift: shifted.reverse | hd tl last ---> shifted hd | tl last
    def shift {
      shifted ::= rest.head
      rest = rest.tail
    }
    while (shifted.nonEmpty || rest.nonEmpty) {
      rest match {
        case Nil =>
          // reduce on the right: before e o | last ---> before | (e o last)
          val (e,o) = shifted.head
          val eolast = Application(BaseOperator(o,null),List(e,last))
          shifted = shifted.tail
          last = eolast
        case (e2,o2) :: tl =>
          if (shifted.isEmpty) {
            shift
          } else {
            val (e1,o1) = shifted.head
            // before e1 o1 | e2 o2 tl last
            if (o1.precedence >= o2.precedence) {
              // reduce on the left: ---> before (e1 o1 e2) o2 | tl last
              val e1o1e2 = Application(BaseOperator(o1,null),List(e1,e2))
              shifted = (e1o1e2,o2) :: shifted.tail
              rest = tl
            } else if (o1.precedence < o2.precedence) {
              // shift: ---> before e1 o1 e2 o2 | tl last
              shift
            }
          }
      }
    }
    last
  }

  def parseType(implicit ctx: Context): Type = addRef {
    val tp = if (startsWith("int")) {skip("int"); IntType}
      //else if (startsWith("float")) {skip("float"); FloatType}
      //else if (startsWith("char")) {skip("char"); CharType}
      else if (startsWithS("rat")) RatType
      else if (startsWithS("string")) StringType
      else if (startsWithS("bool")) BoolType
      else if (startsWithS("empty")) EmptyType
      else if (startsWithS("list[")) {
        val y = parseType
        skip("]")
        ListType(y)
      }
      else if (startsWithS("Option[")) {
        val y = parseType
        skip("]")
        OptionType(y)
      } else if (startsWith("(")) {
        skip("(")
        val ys = parseList(parseType, ",", ")")
        skip(")")
        ys match {
          case Nil => UnitType
          case List(a) => a
          case ys => ProdType(ys)
        }
      } else if (startsWithS("|")) {
        val t = parseTheory
        trim
        skip("|")
        ClassType(t)
      } else {
        val own = parseExpression
        if (startsWithS(".")) {
          val tp = parseType
          OwnedType(tp, own)
        } else own match {
          case r: ClosedRef => r
          case r: OpenRef => r
          case _ => fail("type expected")
        }
      }
    trim
    if (startsWith("->")) {
      skip("->")
      val out = parseType
      tp match {
        case ProdType(ys) => FunType(ys,out)
        case _ => FunType(List(tp),out)
      }
    } else
      tp
  }
}
