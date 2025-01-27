package info.kwarc.p

/* Concrete syntax

   module M {
    decls
   }              modules
   theory M {
    decls
   }              theories (same as modules except that they may be instantiated)
   include M      include of a theory into a theory

   type a [=A]    type declaration
   val c[:A][=t]  constant declaration, type will be inferred if omitted, val keyword can be omitted

   void, unit, int, rat, bool, string
                  base types as usual
   int[l;u]       integer interval

   + * - / & | == != <= >= < > -: :- in
                  operators as usual

   any            supertype of all types
   exc            type of exception

   A -> B
   (A,...) -> B
   (x:A,...) -> B dependent function type
   (x:A,...) -> t
   x -> t         function
   f(t,...)       application
   
   (x:A,...)
   (A,...)        dependent product type
   (t,...)        tuple
   t(n)           projection (parsed as Application and disambiguated by Checker)
   
   C[A]           collection type of kind C, e.g., List[A], Set[A], Option[A],  ([A], A? shortcut for List[A], Option[A])
   [t,...]        collection, e.g., list, set, ...
   l[i]           list access

   M{decls}      new instance of M, decls must define all remaining abstract fields
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

                 control flow as usual
   val x[:A]=t
   var x[:A]=t   new variable (mutable if 'var')
   p = e         assignment of e to pattern p
   while (c) {b}
   if (c) {t} [else {e}]
   for (x in L) {b}
   return e
   throw e
   e match {case p -> e, ...}
   e catch {case p -> e, ...}
 */

/**
  * the context passed during parsing
  * @param contexts bound variables in stack of regions
  * @param allowStatement if false, restrict expression-parsing to declarative expressions (as opposed to statements like while, return)
  * @param allowWeakPostops if false, force bracketing of infix operators in expressions
  *                    this is mutable to allow toggling it back for subexpressions
  */
case class PContext(contexts: List[LocalContext], allowStatement: Boolean, var allowWeakPostops: Boolean) {
  def append(vd: VarDecl): PContext = append(LocalContext(vd))
  def append(ctx: LocalContext): PContext = copy(contexts = contexts.head.append(ctx)::contexts.tail)
  def pop() = copy(contexts = contexts.tail).append(contexts.head) // TODO: type not correct (but irrelevant anyway)
  def push() = copy(contexts = LocalContext.empty::contexts)
  def setAllowStatement(b: Boolean) = copy(allowStatement = b)
  def noWeakPostops = copy(allowWeakPostops = false)
}
object PContext {
  def empty = PContext(List(LocalContext.empty), false, true)
}

object Parser {
  def file(f: File,eh: ErrorHandler) = {
    val p = new Parser(f.toSourceOrigin, getFileContent(f), eh)
    Vocabulary(p.parseDeclarations)
  }

  def getFileContent(f: File) = {
    val txt = File.read(f)
    if (f.getExtension contains ("tex")) Tex.detexify(txt) else txt
  }

  def text(so: SourceOrigin,s: String,eh: ErrorHandler) = {
    val p = new Parser(so,s,eh)
    Vocabulary(p.parseDeclarations)
  }

  def expression(origin: SourceOrigin,s: String,eh: ErrorHandler) = {
    val p = new Parser(origin,s,eh)
    p.parseExpression(PContext.empty)
  }
}

object Tex {
  /** parses a literate UPL file
    * UPL content must be placed in
    * - \begin{upl}...\end{upl} blocks, where the begin/end macros must occur on lines by themselves
    * - \uplinlineC...C for some character C, where the command must not span multiple lines
    * Non-UPL characters are replaced with " " to keep the character positions the same
    */
  def detexify(txt: String) = {
    val sb = new StringBuilder
    var inUPL = false
    // TODO: might count line endings wrong
    txt.split("\\R").foreach {line =>
      val lineT = line.trim
      val take = if (!inUPL && lineT.startsWith(uplStart)) {
        inUPL = true
        Some(false)
      } else if (inUPL && lineT.startsWith(uplEnd)) {
        inUPL = false
        Some(false)
      } else if (!inUPL && lineT.startsWith(moduleBegin)) {
        var i = lineT.indexWhere(c => c == ',' || c == ']')
        if (i == -1) i = i+lineT.length
        val name = lineT.substring(moduleBeginLen,i)
        sb.append("module " + name + " {" + toSpaces(line.drop(7 + name.length + 2)) + "\n")
        None
      } else if (!inUPL && lineT.startsWith(moduleEnd)) {
        sb.append("}" + toSpaces(line.drop(1)) + "\n")
        None
      } else if (inUPL) {
        Some(true)
      } else {
        Some(false)
      }
      if (take contains true) sb.append(line + "\n")
      else if (take contains false) {
        var index = 0
        val len = line.length
        val lineB = new StringBuilder
        var leaveUPLat: Option[Character] = None
        while (index < len) {
          if (leaveUPLat contains line(index)) {
            leaveUPLat = None
            lineB.append(" ")
            index += 1
          } else if (leaveUPLat.isDefined) {
            lineB.append(line(index))
            index += 1
          } else if (index + uplinlineLen < len && line.substring(index,index + uplinlineLen) == uplinline) {
            lineB.append(toSpaces(uplinline))
            index += uplinlineLen
            if (index < len) {
              leaveUPLat = Some(line(index))
              lineB.append(" ")
              index += 1
            }
          } else {
            lineB.append(" ")
            index += 1
          }
          // assert(lineB.toString.length == index)
        }
        sb.append(lineB.toString + "\n")
      }
    }
    // assert(txt.length == sb.toString.length)
    sb.toString
  }
  def toSpaces(s: String) = s.map(_ => ' ').mkString("")
  val moduleBegin = "\\begin{smodule}[id="
  val moduleBeginLen = moduleBegin.length
  val moduleEnd = "\\end{smodule}"
  val uplinline = "\\uplinline"
  val uplinlineLen = uplinline.length
  val uplStart = "\\begin{upl}"
  val uplEnd = "\\end{upl}"
}

class Parser(origin: SourceOrigin, input: String, eh: ErrorHandler) {
  private var index = 0
  private val inputLength = input.length
  override def toString = input.substring(index)
  case class Error(msg: String) extends SError(makeRef(index), msg)
  private case class Abort() extends Exception
  def reportError(msg: String) = {
    val e = Error(msg + "; found " + input.substring(index))
    eh(e)
  }
  def fail(msg: String) = {
    reportError(msg)
    throw Abort()
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
    if (!startsWith(s)) {
      reportError("expected " + s)
    } else {
      index += s.length
    }
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
        val d = try {
          parseDeclaration
        } catch {
          case Abort() => return decls.reverse // unclear how we could recover here
        }
        decls ::= d
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

  def parseVarDecl(mutable: Boolean, nameMandatory: Boolean)(implicit ctxs: PContext): VarDecl = addRef {
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

  def parseContext(namesMandatory: Boolean)(implicit ctxs: PContext): LocalContext = addRef {
    val vds = parseList(parseVarDecl(false, namesMandatory), ",", ")")
    LocalContext.make(vds)
  }

  def parseTheory(implicit ctxs: PContext): Theory = addRef {
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
    val allowWeakPostops = ctxs.allowWeakPostops
    ctxs.allowWeakPostops = true // only active for one level
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
          if (!allowS) reportError("else branch expected")
          None
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
        if (ctxs.contexts.length <= 1) reportError("eval outside quotation")
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
      val strongPostops = List(".","(","[","{","°")
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
          if (!atEnd && next == ' ') {
            // . only works if followed by identifier; this allows using ". " in a quantifier without ambiguity
            index = btp
            tryPostOps = false
          } else {
            val nB = index
            val n = parseName
            if (n.isEmpty) fail("identifier expected")
            val owned = setRef(ClosedRef(n),nB)
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
              val sds = ds.flatMap {
                case sd: SymbolDeclaration => List(sd)
                case _ => reportError("symbol declaration expected"); Nil
              }
              Instance(ExtendedTheory(p,sds).copyFrom(exp))
            case None =>
              val e = parseExpression(ctxs.push()) // in e{q}, q is a closed expression in a different theory
              OwnedExpr(exp,null,e)
          }
          skip("}")
        } else if (startsWithS("°")) {
          // Andrews' dot
          val a = parseExpression
          exp = Application(exp,List(a))
        }
      } // end while
      trim
      if (!allowWeakPostops) return exp
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
          val cs = parseList(parseMatchCase,"}",false).filterNot(_==null)
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

  def parseMatchCase(implicit ctxs: PContext) = addRef {
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
      case _ => reportError("match case expected"); null
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
            // special case of right-associative operators of the same precedence
            val associateRight = o1.precedence == o2.precedence && o1.rightAssociative && o2.rightAssociative
            if (o1.precedence >= o2.precedence && !associateRight) {
              // reduce on the left: ---> before (e1 o1 e2) o2 | tl last
              val bo1 = BaseOperator(o1,Type.unknown())
              bo1.loc = l1
              val e1o1e2 = Application(bo1,List(e1,e2))
              shifted = (e1o1e2,o2,l2) :: shifted.tail
              rest = tl
            } else if (o1.precedence < o2.precedence || associateRight) {
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
          case List(vd) if vd.anonymous => vd.tp
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
          val exp = parseExpression(ctxs.noWeakPostops)
          // The above parses e.tp and e{tp} into OwnedExpr.
          // Setting noWeakPostops avoids parsing -> and other, which we want to handle ourselves.
          // We can only turn some of those into OwnedType: e{tp} only if tp is a reference.
          // Similarly, it parses M{ds} into Instance, which becomes ClassType
          val tp = exp match {
            case r: ClosedRef => r
            case o: OpenRef => o
            case OwnedExpr(o,d,r: ClosedRef) => OwnedType(o,d,r)
            case OwnedExpr(o,d,r: OpenRef) => OwnedType(o,d,r)
            case Instance(thy) => ClassType(thy)
            case _ => reportError("type expected"); AnyType
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

object Keywords {
  val openModule = "module"
  val closedModule = "theory"
  val include = "include"
  val totalInclude = "realize"
  val mutableExprDecl = "mutable"
  val typeDecl = "type"
}