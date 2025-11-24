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
  val weakPostops = List("=","->","==","!=", "match", "catch")
  val conflictingInfixes = Operator.infixes.map(_.symbol).filter(o => weakPostops.exists(o.startsWith))

  def file(f: File,eh: ErrorHandler): TheoryValue = {
    val p = new Parser(f.toSourceOrigin, getFileContent(f), eh)
    TheoryValue(p.parseAll(p.parseDeclarations(false)))
  }

  def getFileContent(f: File) = {
    val txt = File.read(f)
    if (f.getExtension contains ("tex")) Tex.detexify(txt) else txt
  }

  def text(so: SourceOrigin, s: String, eh: ErrorHandler): TheoryValue = {
    val p = new Parser(so,s,eh)
    p.addRef{
      val ds = if (!so.isStandalone) {
        p.parseAll(p.parseExpressionOrDeclarations("_" + so.fragment.hashCode.abs))
      } else {
        p.parseAll(p.parseDeclarations(false))
      }
      TheoryValue(ds)
    }
  }

  def expression(so: SourceOrigin, s: String, eh: ErrorHandler): Expression = {
    val p = new Parser(so,s,eh)
    p.parseAll(p.parseExpression(PContext.empty))
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
    val found =
      if (index < inputLength - 1) input.substring(index,Math.min(index+20,inputLength))
      else "no remaining input."
    val e = Error(msg + "; found " + found)
    eh(e)
  }
  def fail(msg: String) = {
    reportError(msg)
    throw Abort()
  }

  def makeRef(from: Int) = {
    var to = index // the end of the source region (exclusive)
    while (to > 0 && input(to-1).isWhitespace) to -= 1 // remove trailing whitespace from source region
    Location(origin, from, to)
  }
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

  // n character lookahead
  def nextAfter(n: Int) = if (index+n < inputLength) Some(input(index+n)) else None

  // string s occurs at the current index in the input
  // if s is only letters, we additionally check that no name char follows
  def startsWith(s: String): Boolean = {
    val isKeyword = s.nonEmpty && s.forall(_.isLetter)
    val b = index+s.length <= input.length && input.substring(index, index+s.length) == s
    if (b && isKeyword) index+s.length == inputLength || !isNameChar(input(index+s.length))
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

  /*+ skip all whitespace and comments, return true if newline crossed */
  def trim: Boolean = {
    var newlineSeen = false
    while (!atEnd && (next.isWhitespace || startsWith("//"))) {
      if (next.isWhitespace) {
        if (next == '\n') newlineSeen = true
        index += 1
      }
      else {
        while (!atEnd && next != '\n') index += 1
      }
    }
    newlineSeen
  }

  def startsWithInfixOperator = Operator.infixes.exists(o => startsWith(o.symbol))

  /** the whitespace before the current index contains a newline */
  def newlineBefore: Boolean = {
    var i = index-1
    while (i>0) {
      val c = input(i)
      if (!c.isWhitespace) return false
      if (c == '\n') return true
      i -= 1
    }
    false
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

  // check if input left after parsing
  def parseAll[A](parse: => A) = {
    val a = parse
    if (!atEnd) reportError("expected end of input")
    a
  }

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

  def parseWhile(p: Char => Boolean) = {
    val start = index
    while (!atEnd && p(next)) index += 1
    input.substring(start,index)
  }

  def isNameChar(c: Char) = c.isLetterOrDigit || c == '_'

  def parseName = {trim; parseWhile(isNameChar)}

  def parsePath: Path = addRef {
    val ns = parseList(parseName, ".", " ")
    Path(ns)
  }

  import Keywords._

  /** check if a declaration follows */
  def startsWithDeclaration = {
    val backtrackPoint = index
    trim
    val isDecl = allDeclKeywords.exists(startsWith) || {
      val n = parseName
      trim
      n.nonEmpty && (startsWith(":") || startsWith("="))
    }
    index = backtrackPoint
    isDecl
  }

  def parseExpressionOrDeclarations(defaultName: String) = {
    trim
    if (atEnd) Nil else if (startsWithDeclaration) parseDeclarations(false)
    else {
      val e = parseExpression(PContext.empty)
      List(ExprDecl(defaultName,Type.unknown(),Some(e),Modifiers(false,false,false)))
    }
  }

  def parseDeclaration(implicit closed: Boolean): Declaration = addRef {
    val mods = Modifiers(closed, false, false)
    if (startsWithAny(closedModule,openModule)) parseModule
    else if (startsWithAny(include,totalInclude)) parseInclude
    else if (startsWithS(typeDecl)) parseTypeDecl(mods)
    else if (startsWithS(mutableExprDecl)) parseExprDecl(mods.copy(mutable=true))
    else if (startsWithS(exprDecl)) {
      trim
      val n = parseWhile(c => !c.isWhitespace)
      if (n.isEmpty) fail("name expected")
      parseExprDecl(mods, Some(n))
    }
    else if (startsWithDeclaration) parseExprDecl(mods)
    else fail("declaration expected")
  }

  def parseDeclarations(implicit closed: Boolean): List[Declaration] = {
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
    val decls = parseDeclarations(closed)
    trim
    skip("}")
    Module(name, closed, decls)
  }

  def parseInclude: Include = {
    implicit val ctx = PContext.empty
    val rz = skipEither(totalInclude,include)
    val dom = parseTheory
    trim
    val dfO = if (!rz && startsWithS("=")) {
      Some(parseExpression)
    } else {
      None
    }
    Include(dom, dfO, rz)
  }
  /** theory expressions are a subset of expressions in the AST */
  def parseTheory(implicit ctxs: PContext): Theory = expressionToTheory(parseExpression)
  private def expressionToTheory(exp: Expression): Theory = exp match {
    case r: Ref => r
    case OwnedExpr(o,d,e) => OwnedTheory(o,d,expressionToTheory(e)).copyFrom(exp)
    case _ => fail("expected theory, found expression")
  }

  def parseExprDecl(mods: Modifiers, nameAlreadyParsed: Option[String] = None): ExprDecl = {
    val name = nameAlreadyParsed getOrElse parseName
    val args = if (startsWith("(")) Some(parseBracketedContext(PContext.empty)) else None
    trim
    val tp = if (startsWithS(":")) {
      parseType(PContext.empty)
    } else Type.unknown()
    trim
    val vl = if (startsWithS("=")) {
      Some(parseExpression(PContext.empty))
    } else None
    val (atp,avl) = args match {
      case None => (tp,vl)
      case Some(lc) => (FunType(lc,tp), vl map {v => Lambda(lc,v, true)})
    }
    ExprDecl(name, atp, avl, mods)
  }

  def parseTypeDecl(mods: Modifiers): TypeDecl = {
    val name = parseName
    //val args = parseBracketedContext(PContext.empty)
    trim
    val (tp,df) = if (startsWithS("=")) {
      (Type.unbounded,Some(parseType(PContext.empty)))
    } else if (startsWithS("<")) {
      (parseType(PContext.empty), None)
    } else
      (Type.unbounded, None)
    TypeDecl(name, tp, df, mods)
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

  def parseBracketedContext(implicit ctxs: PContext): LocalContext = {
    trim
    if (startsWithS("(")) {
      val c = parseContext(false)
      skip(")")
      c
    } else {
      LocalContext.empty
    }
  }


  def parseExpressions(open: String, close: String)(implicit ctxs: PContext) = {
    skip(open)
    val es = parseList(parseExpression, ",", close)
    skip(close)
    es
  }

  def parseExpression(implicit ctxs: PContext): Expression = addRef {
    try {
      parseExpressionInner
    } catch {
      case Abort() => UndefinedValue(Type.unknown()) // give up on the subexpression but parse the rest
    }
  }
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
    var seen: List[(Expression,InfixParsable,Location)] = Nil
    val allExpBeginAt = index
    while (true) {
      trim
      val expBeginAt = index
      var exp: Expression =
        if (startsWithS(".")) {
          if (!atEnd && isNameChar(next)) {
            // .id is OpenRef
            OpenRef(parsePath)
          } else {
            // . is this, .. is parent and so on
            var l = 1
            while (startsWithS(".")) {l += 1}
            trim
            // .a is this.a, ..a is parent.a, and so on; thus: if .id follows, we keep the last .
            if (!atEnd && isNameChar(next)) index-=1
            This(l)
          }
      } else if (startsWithS("§{")) {
        val ds = parseDeclarations(true)
        trim
        skip("}")
        Instance(Theory(ds))
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
      } else if (startsWithS(Keywords.mutableVarDecl)) {
        trim
        parseVarDecl(true, true)
      } else if (startsWithS(Keywords.varDecl)) {
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
        val s = parseWhile(_ != '"')
        skip("\"")
        StringValue(s)
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
      } else if (startsWithS("???")) {
        UndefinedValue(Type.unknown())
      } else if (!atEnd && (next.isDigit || next == '-')) {
        val begin = index
        if (next == '-') skip("-")
        var seenDot = false
        while (!atEnd && (next.isDigit || (!seenDot && next == '.'))) {
          if (next == '.') seenDot = true
          index += 1
        }
        val s = input.substring(begin,index)
        if (seenDot)
          FloatValue(s.toFloat)
        else
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
      } else if (startsWithAny("[" :: CollectionKind.allKeywords :_*)) {
          val kindO = if (startsWith("[")) None
          else CollectionKind.allKinds.find(k => startsWithS(k._1)).map(_._2)
          val es = parseExpressions("[","]")
          val k = kindO.getOrElse {if (es.length > 1) CollectionKind.List else CollectionKind.Option}
          CollectionValue(es,k)
      } else if (startsWithS("`")) {
        if (ctxs.contexts.length <= 1) reportError("eval outside quotation")
        val e = parseExpression(ctxs.pop())
        skip("`")
        Eval(e)
      } else if (!atEnd && Parsable.circumfixClose(next).isDefined) {
        val open = parseWhile(Parsable.isCircumfixChar)
        val op = new PseudoCircumfixOperator(open)
        val bo = BaseOperator(op,Type.unknown())
        val es = parseExpressions("", op.close)
        Application(bo, es)
      } else {
        //  symbol/variable/module reference
        val n = parseName
        if (n.isEmpty) fail("name expected")
        trim
        if (startsWith(":") && !startsWithInfixOperator) {
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
      // if expressions are split over multiple lines, strong postops must occur at the end of the line, not the beginning
      // also, some expression can never be followed by a strong postop
      var tryPostOps = !newlineBefore && (exp match {
        case _:BaseValue | _: Block | _: Assign | _: VarDecl | _:While | _:For | _: Return => false
        case _ => true
      })
      val strongPostops = List(".","(","[","{","°")
      while (tryPostOps && {trim; startsWithAny(strongPostops:_*)}) {
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
          // check if there was a Ref before
          def asRef(e: Expression): Option[Ref] = e match {
            case OwnedExpr(e,_,ClosedRef(n)) => asRef(e).map {
              case OpenRef(p) => OpenRef(p/n)
              case ClosedRef(m) => OpenRef(Path(m) / n)
              case VarRef(m) => OpenRef(Path(m) / n)
            }
            case r: Ref => Some(r)
            case _ => None
          }
          asRef(exp) match {
            case Some(r) if startsWithDeclaration =>
              // p{decls}
              val ds = parseDeclarations(true)
              val sds = ds.flatMap {
                case sd: SymbolDeclaration => List(sd)
                case _ => reportError("symbol declaration expected"); Nil
              }
              exp = Instance(Theory(Include(r)::sds)).copyFrom(exp)
            case _ =>
              // in e{q}, q is a closed expression in a different theory
              val e = parseExpression(ctxs.push())
              exp = OwnedExpr(exp,null,e)
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
      if (startsWithAny(Parser.weakPostops:_*) && !startsWithAny(Parser.conflictingInfixes:_*)) {
        exp = disambiguateInfixOperators(seen.reverse,exp)
        setRef(exp,allExpBeginAt)
        val expWP = if (startsWithS("=")) {
          val df = parseExpression
          Assign(exp,df)
        } else if (startsWithS("->")) {
          // decls -> body is a Lambda, pattern -> body is a MatchCase
          def asVarDecls(e: Expression,top: Boolean): Option[List[VarDecl]] = e match {
            case UnitValue if top => Some(Nil)
            case Tuple(es) if top =>
              val esV = es.map(e => asVarDecls(e,false))
              if (esV.forall(_.isDefined)) Some(esV.flatMap(_.get))
              else None
            case e =>
              val vd = e match {
                case vd: VarDecl => vd
                case VarRef(n) => VarDecl(n,Type.unknown()).copyFrom(e)
                case ClosedRef(n) => VarDecl(n,Type.unknown()).copyFrom(e)
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
              Lambda(ctx,b,false)
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
        parseInfixO(Operator.infixes) match {
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
      case Lambda(ins,bd,_) =>
        // awkward: if parseExpression was able to turn the pattern into a lambda, undo that here
        val p = if (ins.decls.length != 1)
          Tuple(Util.reverseMap(ins.decls)(_.toRef))
        else
          VarRef(ins.decls.head.name)
        MatchCase(null, p.copyFrom(ins), bd)
      case e => reportError("match case expected"); MatchCase(null,VarRef(""), e)
    }
  }

  def parseInfixO(os: List[InfixParsable]): Option[InfixParsable] = {
    val found = os.find {o => startsWith(o.symbol) && nextAfter(o.length).forall(!Parsable.isInfixChar(_))}
    found match {
      case Some(f) =>
        skip(f.symbol)
        found
      case None =>
        val op = parseWhile(Parsable.isInfixChar)
        if (op.nonEmpty) {
          Some(new PseudoInfixOperator(op))
        } else {
          None
        }
    }
  }

  // a shift-reduce parser of e1 o1 ... en on last
  def disambiguateInfixOperators(eos: List[(Expression,InfixParsable,Location)], lastExp: Expression): Expression = {
    // invariant: eos last = shifted rest last
    var shifted: List[(Expression, InfixParsable, Location)] = Nil
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
    var tp = addRef {
      if (startsWith(".") && !startsWith("..")) {
        skip(".")
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
          IntervalType(l, u)
        } else
          NumberType.Int
      }
      //else if (startsWith("float")) {skip("float"); FloatType}
      //else if (startsWith("char")) {skip("char"); CharType}
      else if (startsWithS("nat")) NumberType.Nat
      else if (startsWithS("rat")) NumberType.Rat
      else if (startsWithS("comp")) NumberType.RatComp
      else if (startsWithS("float")) NumberType.Float
      else if (startsWithS("string")) StringType
      else if (startsWithS("bool")) BoolType
      else if (startsWithS("empty")) EmptyType
      else if (startsWithS("exn")) ExceptionType
      else if (startsWithS("any")) AnyType
      else if (startsWithAny("[" :: CollectionKind.allKeywords: _*)) {
        val kind = if (startsWith("[")) CollectionKind.List
        else CollectionKind.allKinds.find(k => startsWithS(k._1)).get._2
        skip("[")
        val y = parseType
        skip("]")
        CollectionType(y, kind)
      } else if (startsWith("(")) {
        val ys = parseBracketedContext
        ys.decls match {
          case Nil => UnitType
          case List(vd) if vd.anonymous => vd.tp
          case _ => ProdType(ys)
        }
      } else if (startsWithS("|-")) {
        // TODO: this awkwardly parses c: |- F = p as c : |- (F = p) and then fails with a confusing error
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
          // We reuse expression parsing for 3 reasons:
          // - reuse the code for parsing Refs
          // - owned types starts with an expression
          // - expr-to-type coercion allows expressions in type-positions
          // Setting noWeakPostops avoids parsing -> and other operators, which we want to handle ourselves.
          index = backtrackPoint
          val exp = parseExpression(ctxs.noWeakPostops)
          val tp = exp match {
            case r: Ref => r
            // The above falsely parses e.tp and e{tp} into OwnedExpr. We can turn only some of those into OwnedType:
            case OwnedExpr(o, d, r: Ref) => OwnedType(o, d, r)
            // Similarly, it parses M{ds} into Instance, which we can turn into ClassType.
            case Instance(thy) => ClassType(thy)
            // Any other expression, we coerce into a type.
            // This coercion should happen during type-checking (and it does for Refs and OwnedType(_,_,Ref)),
            // but because it changes Scala-type, we have to do it here already.
            case _: VarRef | _: Application | _: Projection | _: ListElem => MagicFunctions.typeOf(exp, null)
            case _ => reportError("type expected"); AnyType
          }
          tp.copyFrom(exp)
        }
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
  val exprDecl = "val"
  val mutableExprDecl = "mutable"
  val varDecl = "val"
  val mutableVarDecl = "var"
  val typeDecl = "type"
  val allDeclKeywords = List(openModule,closedModule,include,totalInclude,mutableExprDecl,typeDecl)
}