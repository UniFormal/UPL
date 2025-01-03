package info.kwarc.p

/* Concrete syntax
   (A,...) -> B
   A -> B         function type
   (x:A,...) -> t
   x -> t         function
   f(t,...)       application
   
   (A,...)        product type
   (t,...)        tuple
   t(n)           projection (parsed as Application and disambiguated by Checker)
   
   [A]            list type
   [t,...]        list
   l[i]           list access

   A?             option type
   t?             option value
   ?              none value
   
   M{decls}      instance
   Instance{exp}
   Instance{type}
   Instance.id    instance access (OwnedXXX)

   M{type}
   M.id          quotation type, variables not available in the context are
   M{exp}
   M.id          quotation
       (all parsed as OwnedXXX and disambiguated by Checker)
   `exp`:        eval

   not implemented yet
   I@q:          instance-quotation pair 
 */

case class PContext(contexts: List[LocalContext], allowStatement: Boolean) {
  def append(vd: VarDecl): PContext = append(LocalContext(vd))
  def append(ctx: LocalContext): PContext = copy(contexts = contexts.head.append(ctx)::contexts.tail)
  def pop() = copy(contexts = contexts.tail)
  def push() = copy(contexts = LocalContext.empty::contexts)
  def setAllowStatement(b: Boolean) = copy(allowStatement = b)
}
object PContext {
  def empty = PContext(List(LocalContext.empty), false)
}

object Parser {
  def file(f: File) = {
    val p = new Parser(f.toSourceOrigin, File.read(f))
    Module.anonymous(p.parseDeclarations)
  }
  def expression(origin: String, s: String) = {
    val p = new Parser(SourceOrigin(origin), s)
    p.parseExpression(PContext.empty)
  }
}

class Parser(origin: SourceOrigin, input: String) {
  private var index = 0
  private val inputLength = input.length
  override def toString = input.substring(index)

  case class Error(msg: String) extends PError(msg)
  def fail(msg: String) = {
    throw Error(msg + "; found " + input.substring(index))
  }

  def makeRef(from: Int) = Location(origin, from, index)
  def addRef[A<:SyntaxFragment](sf: => A): A = {
    trim
    val from = index
    val a = sf
    setRef(a, from)
    a
  }
  def setRef(sf: SyntaxFragment, from: Int): sf.type = {
    sf.loc = makeRef(from)
    sf
  }

  // all input has been parsed
  def atEnd = {index == inputLength}

  // next character to parse
  def next = input(index)


  // string s occurs at the current index in the input
  // if s is only letters, we additionally check that no id char follows
  def startsWith(s: String): Boolean = {
    val isKeyword = s.nonEmpty && s.forall(_.isLetter)
    val b = index+s.length <= input.length && input.substring(index, index+s.length) == s
    if (b && isKeyword) (index+s.length == input.length || !Path.isIdChar(input(index+s.length)))
    else b
  }
  /** test for some strings, and if found, skip and trim */
  def startsWithS(s: String): Boolean = {
    val b = startsWith(s)
    if (b) {skip(s); trim}
    b
  }

  /** like startsWith but for multiple options */
  def startsWithAny(k: String*) = k.toList.exists(startsWith)
  /** skips either of two options, true if it was the first one */
  def skipEither(t: String, f: String): Boolean = {
    if (startsWithS(t)) true else {skipT(f); false}
  }

  // skip all whitespace and comments
  def trim: Unit = {
    while (!atEnd && (next.isWhitespace || startsWith("//")))
      if (next.isWhitespace) index += 1
      else {
        while (!atEnd && next != '\n') index += 1
      }
  }

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
    while (!atEnd && (next.isLetterOrDigit || next == '_')) index += 1
    input.substring(begin,index)
  }

  def parsePath: Path = addRef {
    val ns = parseList(parseName, ".", " ")
    Path(ns)
  }

  object Keywords {
    val openModule = "module"
    val closedModule = "class"
    val include = "include"
    val totalInclude = "realize"
    val mutableExprDecl = "mutable"
    val typeDecl = "type"
  }
  import Keywords._

  def parseDeclaration: Declaration = addRef {
    if (startsWithAny(closedModule,openModule)) parseModule
    else if (startsWithAny(include,totalInclude)) parseInclude
    else if (startsWithS(typeDecl)) parseTypeDecl
    else if (startsWithS(mutableExprDecl)) parseExprDecl(true)
    else if (!atEnd && next.isLetter) parseExprDecl(false)
    else fail("declaration expected")
  }

  def parseDeclarations: List[Declaration] = {
    var decls: List[Declaration] = Nil
    var break = false
    while (!break) {
      trim
      if (atEnd || startsWith("}")) {break = true}
      else {
        if (startsWith(",")) skip(",")
        decls ::= parseDeclaration
      }
    }
    decls.reverse
  }

  def parseModule: Module = {
    val closed = skipEither(closedModule,openModule)
    val name = parseName
    trim
    skip("{")
    val decls = parseDeclarations
    trim
    skip("}")
    Module(name, closed, decls)
  }

  def parseInclude: Include = {
    implicit val ctx = PContext.empty
    val rz = skipEither(totalInclude,include)
    val dom = parsePath
    trim
    val dfO = if (!rz && startsWithS("=")) {
      Some(parseExpression)
    } else {
      None
    }
    Include(dom, dfO, rz)
  }

  def parseExprDecl(mutable: Boolean): ExprDecl = {
    val name = parseName
    trim
    val tp = if (startsWithS(":")) {
      parseType(PContext.empty)
    } else Type.unknown()
    trim
    val vl = if (startsWithS("=")) {
      Some(parseExpression(PContext.empty))
    } else None
    ExprDecl(name, tp, vl, mutable)
  }

  def parseTypeDecl: TypeDecl = {
    val name = parseName
    trim
    val (tp,df) = if (startsWithS("=")) {
      (Type.unbounded,Some(parseType(PContext.empty)))
    } else if (startsWithS("<")) {
      (parseType(PContext.empty), None)
    } else
      (Type.unbounded, None)
    TypeDecl(name, tp, df)
  }

  def parseVarDecl(mutable: Boolean, nameMandatory: Boolean)(implicit ctxs: PContext): VarDecl = {
    val noStatements = ctxs.setAllowStatement(false)
    val backtrackPoint = index
    val n = parseName
    trim
    if (!startsWithAny(":","=") && !nameMandatory && !mutable) {
      // n is not actually a variable name, treat this as anonymous var decl
      index = backtrackPoint
      val tp = parseType(noStatements)
      VarDecl.anonymous(tp)
    } else {
      val tp = if (startsWithS(":")) {
        parseType(noStatements)
      } else Type.unknown()
      val df = if (startsWithS("=")) {
        Some(parseExpression(noStatements))
      } else None
      VarDecl(n,tp,df,mutable)
    }
  }

  def parseContext(namesMandatory: Boolean)(implicit ctxs: PContext): LocalContext = {
    val vds = parseList(parseVarDecl(false, namesMandatory), ",", ")")
    LocalContext.make(vds)
  }

  def parseTheory(implicit ctxs: PContext): Theory = {
    trim
    val ps = parseList(parsePath, "+", "|")
    Theory(ps.map(p => Include(p)))
  }

  def parseExpressions(open: String, close: String)(implicit ctxs: PContext) = {
    skip(open)
    val es = parseList(parseExpression, ",", close)
    skip(close)
    es
  }

  def parseExpression(implicit ctxs: PContext): Expression = addRef {parseExpressionInner}
  def parseBracketedExpression(implicit ctxs: PContext) = {
    skip("(")
    val e = parseExpression
    skip(")")
    e
  }
  // needed because addRef does not work with return-statements
  private def parseExpressionInner(implicit ctxs: PContext): Expression = {
    val allowS = ctxs.allowStatement
    val doAllowS = ctxs.setAllowStatement(true)
    val doNotAllowS = ctxs.setAllowStatement(false)
    var seen: List[(Expression,InfixOperator,Location)] = Nil
    val allExpBeginAt = index
    while (true) {
      trim
      val expBeginAt = index
      var exp: Expression = if (startsWithS(".")) {
        OpenRef(parsePath)
      } else if (startsWithS("{")) {
        var cs: List[Expression] = Nil
        var ctxL = ctxs.setAllowStatement(true)
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
        parseVarDecl(true, true)
      } else if (startsWithS("val")) {
        trim
        parseVarDecl(false,true)
      } else if (startsWithAny("exists","forall")) {
        val univ = skipEither("forall", "exists")
        val vars = parseContext(true)
        skipT(".")
        val body = parseExpression
        Quantifier(univ,vars,body)
      } else if (allowS && startsWithS("while")) {
        val c = parseBracketedExpression
        val b = parseExpression(doAllowS)
        While(c,b)
      } else if (allowS && startsWithS("for")) {
        skipT("(")
        val v = parseName
        trim
        skipT("in")
        val r = parseExpression
        skipT(")")
        val b = parseExpression(doAllowS.append(VarDecl(v,Type.unknown())))
        For(VarDecl(v,Type.unknown()),r,b)
      } else if (startsWithS("if")) {
        val c = parseBracketedExpression
        val th = parseExpression
        trim
        val el = if (startsWithS("else")) {
          Some(parseExpression)
        } else {
          if (!allowS) fail("else branch expected")
          else None
        }
        IfThenElse(c,th,el)
      } else if (allowS && startsWithAny("return","throw")) {
        val thrw = skipEither("throw","return")
        val r = parseExpression
        Return(r,thrw)
      } else if (Operator.prefixes.exists(o => startsWith(o.symbol))) {
        val o = Operator.prefixes.find(o => startsWith(o.symbol)).get
        skip(o.symbol)
        val e = parseExpression
        Application(BaseOperator(o,Type.unknown()),List(e))
      } else if (startsWithS("\"")) {
        val begin = index
        while (!atEnd && next != '"') index += 1
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
      } else if (!atEnd && (next.isDigit || next == '-')) {
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
        val es = parseExpressions("(",")")
        trim
        es match {
          case Nil => UnitValue
          case List(e) => e
          case es => Tuple(es)
        }
      } else if (startsWith("[")) {
        val es = parseExpressions("[","]")
        CollectionValue(es)
      } else if (startsWithS("`")) {
        if (ctxs.contexts.length <= 1) fail("eval outside quotation")
        val e = parseExpression(ctxs.pop())
        skip("`")
        Eval(e)
      } else {
        //  symbol/variable/module reference
        val n = parseName
        trim
        if (startsWith(":") && !Operator.infixes.exists(o => startsWith(o.symbol))) {
          // variable declaration
          skip(":")
          val tp = parseType(doNotAllowS)
          VarDecl(n,tp)
        } else if (n == "_") {
          VarDecl.anonymous(Type.unknown()) // anonymous variable
        } else if (ctxs.contexts.head.domain.contains(n)) {
          VarRef(n) // reference to bound variable
        } else {
          ClosedRef(n)
        }
      } // end exp =
      trim
      // avoid trying to parse nonsense if we can already tell
      var tryPostOps = exp match {
        case _:BaseValue | _: Block | _: Assign | _: VarDecl | _:While | _:For | _: Return => false
        case _ => true
      }
      val strongPostops = List(".","(","[","{")
      while (tryPostOps && startsWithAny(strongPostops:_*)) {
        setRef(exp,expBeginAt) // only the outermost expression gets its source reference automatically
        if (startsWithS("(")) {
          val es = parseExpressions("",")")
          exp = Application(exp,es)
        } else if (startsWithS("[")) {
          val e = parseExpression
          skip("]")
          exp = ListElem(exp,e)
        } else if (startsWith(".")) {
          val btp = index
          skip(".")
          if (!atEnd && next.isWhitespace) {
            // . only works if followed by identifier; this allows using ". " in a quantifier without ambiguity
            index = btp
            tryPostOps = false
          } else {
            val nB = index
            val owned = setRef(ClosedRef(parseName),nB)
            exp = OwnedExpr(exp,null,owned)
          }
        } else if (startsWithS("{")) {
          // conflict between M{decls} and exp{exp}
          // we look back and ahead to see if it is the former, in which case looksLikeInstanceOf.isDefined
          // check if there was a Path before
          def asPath(e: Expression): Option[Path] = e match {
            case OwnedExpr(e,_,ClosedRef(n)) => asPath(e).map(_ / n)
            case ClosedRef(n) => Some(Path(List(n)))
            case _ => None
          }
          var looksLikeInstanceOf = asPath(exp)
          if (looksLikeInstanceOf.isDefined) {
            // check if a declaration follows
            val backtrackPoint = index
            val isDecl = startsWith(typeDecl) || startsWith(mutableExprDecl) || {
              parseName
              trim
              startsWith(":") || startsWith("=")
            }
            if (!isDecl) looksLikeInstanceOf = None
            index = backtrackPoint
          }
          exp = looksLikeInstanceOf match {
            case Some(p) =>
              // p{decls}
              val ds = parseDeclarations
              val sds = ds.collect {
                case sd: SymbolDeclaration => sd
                case _ => fail("symbol declaration expected")
              }
              Instance(ExtendedTheory(p,sds).copyFrom(exp))
            case None =>
              val e = parseExpression(ctxs.push()) // in e{q}, q is a closed expression in a different theory
              OwnedExpr(exp,null,e)
          }
          skip("}")
        }
      } // end while
      trim
      val weakPostops = List("=","->","match", "catch")
      if (startsWithAny(weakPostops:_*) && !startsWith("==")) {
        exp = disambiguateInfixOperators(seen.reverse,exp)
        setRef(exp,allExpBeginAt)
        val expWP = if (allowS && startsWithS("=")) {
          val df = parseExpression
          Assign(exp,df)
        } else if (startsWithS("->")) {
          // decls -> body is a Lambda, pattern -> body is a MatchCase
          def asVarDecls(e: Expression,top: Boolean): Option[List[VarDecl]] = e match {
            case Tuple(es) if top =>
              val esV = es.map(e => asVarDecls(e,false))
              if (esV.forall(_.isDefined)) Some(esV.flatMap(_.get))
              else None
            case e =>
              val vd = e match {
                case vd: VarDecl => vd
                case VarRef(n) => VarDecl(n,Type.unknown())
                case ClosedRef(n) => VarDecl(n,Type.unknown())
                case _ => return None
              }
              Some(List(vd))
          }
          asVarDecls(exp,true) match {
            case None =>
              val b = parseExpression(doAllowS)
              MatchCase(null,exp,b)
            case Some(ins) =>
              val ctx = LocalContext.make(ins)
              val b = parseExpression(doAllowS.append(ctx))
              Lambda(ctx,b)
          }
        } else if (startsWithAny("match","catch")) {
          val handle = skipEither("catch","match")
          skip("{")
          val cs = parseList(parseMatchCase,"}",false)
          skip("}")
          Match(exp,cs,handle)
        } else exp
        return expWP
      } else {
        setRef(exp, expBeginAt)
        val opBegin = index
        parseOperatorO(Operator.infixes) match {
          case None =>
            return disambiguateInfixOperators(seen.reverse,exp)
          case Some(o) =>
            seen ::= (exp,o, makeRef(opBegin))
        }
      }
    } // end while
    null // impossible
  }

  def parseMatchCase(implicit ctxs: PContext) = {
    val e = parseExpression
    e match {
      case mc: MatchCase => mc
      case Lambda(ins,bd) =>
        // awkward: if parseExpression was able to turn the pattern into a lambda, undo that here
        val p = if (ins.decls.length != 1)
          Tuple(Util.reverseMap(ins.decls)(_.toRef))
        else
          VarRef(ins.decls.head.name)
        MatchCase(null, p.copyFrom(ins), bd)
      case _ => fail("match case expected")
    }
  }

  def parseOperatorO[O<:Operator](os: List[O]): Option[O] = {
    var found: Option[O] = None
    os.foreach {o =>
      if (startsWith(o.symbol) && !found.exists(f => f.length > o.length))
        found = Some(o)
    }
    found.foreach {f => skip(f.symbol)}
    found
  }

  // a shift-reduce parser of e1 o1 ... en on last
  def disambiguateInfixOperators(eos: List[(Expression,InfixOperator,Location)], lastExp: Expression): Expression = {
    // invariant: eos last = shifted rest last
    var shifted: List[(Expression, InfixOperator,Location)] = Nil
    var rest = eos
    var last = lastExp
    // shift: shifted.reverse | hd tl last ---> shifted hd | tl last
    def shift = {
      shifted ::= rest.head
      rest = rest.tail
    }
    while (shifted.nonEmpty || rest.nonEmpty) {
      rest match {
        case Nil =>
          // reduce on the right: before e o | last ---> before | (e o last)
          val (e,o,l) = shifted.head
          val bo = BaseOperator(o,Type.unknown())
          bo.loc = l
          val eolast = Application(bo,List(e,last))
          shifted = shifted.tail
          last = eolast
        case (e2,o2,l2) :: tl =>
          if (shifted.isEmpty) {
            shift
          } else {
            val (e1,o1,l1) = shifted.head
            // before e1 o1 | e2 o2 tl last
            if (o1.precedence >= o2.precedence) {
              // reduce on the left: ---> before (e1 o1 e2) o2 | tl last
              val bo1 = BaseOperator(o1,Type.unknown())
              bo1.loc = l1
              val e1o1e2 = Application(bo1,List(e1,e2))
              shifted = (e1o1e2,o2,l2) :: shifted.tail
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

  private val typePostOps = List("->","?")
  def parseType(implicit ctxs: PContext): Type = addRef {
    val tpBegin = index
    var tp = if (startsWithS(".")) {
        OpenRef(parsePath)
      } else if (startsWithS("int")) {
        trim
        if (startsWithS("[")) {
          trim
          val l = if (startsWith(";")) None else Some(parseExpression)
          trim
          skipT(";")
          val u = if (startsWith("]")) None else Some(parseExpression)
          trim
          skip("]")
          IntervalType(l,u)
        } else
          IntType
      }
      //else if (startsWith("float")) {skip("float"); FloatType}
      //else if (startsWith("char")) {skip("char"); CharType}
      else if (startsWithS("rat")) RatType
      else if (startsWithS("string")) StringType
      else if (startsWithS("bool")) BoolType
      else if (startsWithS("empty")) EmptyType
      else if (startsWithS("exn")) ExceptionType
      else if (startsWithAny("[" :: CollectionKind.allKeywords :_*)) {
        val kind = if (startsWith("[")) CollectionKind.List
        else CollectionKind.allKinds.find(k => startsWithS(k._1)).get._2
        skip("[")
        val y = parseType
        skip("]")
        CollectionType(y, kind)
      } else if (startsWith("(")) {
        skip("(")
        val ys = parseContext(false)
        skip(")")
        ys.decls match {
          case Nil => UnitType
          case _ => ProdType(ys)
        }
      } else if (startsWithS("|-")) {
        val e = parseExpression
        ProofType(e)
      } else {
        // conflict between types that start with a name and those starting with an expression, i.e., e{tp} or e.tp
        val backtrackPoint = index
        val n = parseName
        trim
        if (n == "_") {
          Type.unknown()
        } else if (n != "" && !atEnd && typePostOps.exists(startsWith)) {
          // looks like a type that starts with a name
          ClosedRef(n)
        } else {
          index = backtrackPoint
          val exp = parseExpression
          // The above parses e.tp and e{tp} into OwnedExpr.
          // We can only turn some of those into OwnedType: e{tp} only if tp is a reference.
          // Similarly, it parses M{ds} into Instance, which becomes ClassType
          val tp = exp match {
            case r: ClosedRef => r
            case o: OpenRef => o
            case OwnedExpr(o,d,r: ClosedRef) => OwnedType(o,d,r)
            case OwnedExpr(o,d,r: OpenRef) => OwnedType(o,d,r)
            case Instance(thy) => ClassType(thy)
            case _ => fail("type expected")
          }
          tp.copyFrom(exp)
        }
      }
    trim
    // postfix/infix type operators
    while (typePostOps.exists(startsWith)) {
      if (startsWithS("->")) {
        val (ctxR,ins) = tp match {
          case ProdType(ys) => (ctxs.append(ys),ys)
          case y => (ctxs, LocalContext(VarDecl.anonymous(y)))
        }
        val out = parseType(ctxR) // makes -> right-associative and dependent
        tp = FunType(ins,out)
      } else if (startsWithS("?")) {
        setRef(tp, tpBegin)
        tp = CollectionType(tp, CollectionKind.Option)
      }
    }
    tp
  }
}
