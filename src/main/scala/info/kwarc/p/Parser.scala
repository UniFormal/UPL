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
   f t ...        whitespace-application
   
   (x:A,...)
   (A,...)        dependent product type
   (t,...)        tuple
   t(n)           projection (parsed as Application and disambiguated by Checker)
   
   C[A]           collection type of kind C, e.g., List[A], Set[A], Option[A],  ([A], A? shortcut for List[A], Option[A])
   [t,...]        collection, e.g., list, set, ...
   l[i]           list access

   custom operator application  (op- must be closing bracket corresponding to op)
   op              nullfix
   op t            prefix
   t op            postfix
   t op t          infix (precedence decided based on op-length: number of characters + surrounding space)
   op t,... op-    circumfix
   t op t, ... op- applyfix
   op ctx. body    bindfix
   id ctx. body    whitespace-binding

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
   e match {p -> e ...}
   e catch {p -> e ...}


   operator parsing:
   1) after an expression
      take all operators until a bracket, term-ender (,;), or a non-operator
      if open bracket: by itself -> applyfix
                       after other operators -> circumfix
      if close bracket or term-ender: end of expression, not returned itself
      remaining operators can be null/pre/in/postfix
      - non-empty spacing:
        - asymmetric -> pre/post depending on which side is bigger
        - symmetric -> infix
        - exception: nullfix if in/post after in or pre before in, post after pre, pre after post
 */

/**
  * the context passed during parsing
  * @param contexts bound variables in stack of regions
  * @param inType true if the parsed expression will actually be converted into an expression
  * @param eager Some(true): continue across newline; None: continue across space; Some(false) do not continue across space
  * @param allowStatement if false, restrict expression-parsing to declarative expressions (as opposed to statements like while, return)
  */
case class PContext(contexts: List[LocalContext], inType: Boolean, eager: Option[Boolean], allowStatement: Boolean, terminators: List[String]) {
  def declares(n: String) = contexts.head.declares(n)
  def append(vd: EVarDecl): PContext = append(LocalContext(vd))
  def append(ctx: AbstractLocalContext[_,_]): PContext = copy(contexts = contexts.head.append(ctx.local)::contexts.tail)
  def pop() = copy(contexts = contexts.tail).append(contexts.head) // TODO: type not correct (but irrelevant anyway)
  def push() = copy(contexts = LocalContext.empty::contexts)
}
object PContext {
  def empty = PContext(List(LocalContext.empty), false, None, true, Nil)
}

object Parser {
  val digits = "0123456789".toList

  def file(f: File,eh: ErrorHandler) = {
    val p = new Parser(f.toSourceOrigin, getFileContent(f), eh)
    TheoryValue(p.parseAll(p.parseDeclarations(false)))
  }

  def getFileContent(f: File) = {
    val txt = File.read(f)
    if (f.getExtension contains ("tex")) Tex.detexify(txt) else txt
  }

  def text(so: SourceOrigin, s: String, eh: ErrorHandler): TheoryValue = {
    val p = new Parser(so,s,eh)
    val ds = if (!so.isStandalone) {
      p.parseAll(p.parseExpressionOrDeclarations("_" + so.fragment.hashCode.abs))
    } else {
      p.parseAll(p.parseDeclarations(false))
    }
    TheoryValue(ds).withLocation(Location(so,0,s.length))
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
  case class Error(l: Location, msg: String) extends SError(l, msg)
  private case class Abort() extends Exception
  private case class TrialRunFailed() extends Exception
  private var trialRun = false

  /** report an error at the [[Location]] of `sf` to the [[ErrorHandler]], and continue  */
  def reportError(msg: String, sf: SyntaxFragment): Unit = reportError(msg, sf.loc.from, sf.loc.to)
  /** report an error between `from` and `to` the [[ErrorHandler]], and continue
    * @param to defaults to the current [[index]]
    */
  def reportError(msg: String, from: Int, to: Int = index): Unit = {
    if (trialRun) throw TrialRunFailed()
    val toDisplay: Int = List(to, inputLength, from+20).min
    val found = input.substring(from,toDisplay)
    val e = Error(Location(origin, from, to), msg + "; found " + found)
    eh(e)
  }
  /** report an error between `at` and [[index]] the [[ErrorHandler]], and then throw [[Abort]] */
  def fail(msg: String, at: Int = index) = {
    reportError(msg, at)
    throw Abort()
  }
  /** runs code, returns result if no errors, otherwise backtracks */
  def tryParse[A](code: => A): Option[A] = {
    val trialRunBefore = trialRun
    trialRun = true
    val beg = index
    try {Some(code)}
    catch {case TrialRunFailed() => index = beg; None}
    finally {trialRun = trialRunBefore}
  }

  /** Generate a [[Location]] between `from` and `toD` whithout whitespace */
  def makeRef(from: Int, toD: Int = index) = {
    var to = toD // the end of the source region (exclusive)
    while (to > 0 && input(to-1).isWhitespace) to -= 1 // remove trailing whitespace from source region
    Location(origin, from, to)
  }
  /** Parse a [[SyntaxFragment]], and assign its [[Location]] */
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

  /** all input has been parsed */
  def atEnd = {index == inputLength}
  /** whitespace until end of line or end of input */
  def atEndOfLine: Boolean = {
    var i = index
    while (!atEnd) {
      val c = input.codePointAt(i)
      if (c == '\n') return true
      else if (Character.isWhitespace(c)) i += 1
      else return false
    }
    true
  }

  /** next character to parse, possibly consisting of 2 chars in input */
  def next = input.codePointAt(index)
  /** next character to parse is `c` */
  def nextIs(c: Unicode.UChar) = !atEnd && next == c

  /** take the next character */
  def parseNext = {val c = next; index += Character.charCount(c); Character.toString(c)}
  /** n character lookahead */
  def nextAfter(n: Int) = if (index+n < inputLength) Some(input.codePointAt(index+n)) else None

  /** string s occurs at the current index in the input
    * if s is only letters/symbols, we additionally check that no name char/symbol follows
    * Only tests, does not change [[index]]
    */
  def startsWith(s: String, andSomethingElse: Boolean = true): Boolean = {
    if (s.isEmpty) return true
    val b = index+s.length <= input.length && input.substring(index, index+s.length) == s
    if (!b || !andSomethingElse) b
    else if (s.forall(_.isLetter)) !nextAfter(s.length).exists(isNameChar)
    else if (s.forall(c => Symbols.isMultiOpChar(c.toInt))) !nextAfter(s.length).exists(Symbols.isMultiOpChar)
    else b
  }
  /** test for some strings, and if found, skip and trim */
  def startsWithS(s: String, andSomethingElse: Boolean = true): Boolean = {
    val b = startsWith(s, andSomethingElse)
    if (b) {skip(s); trim}
    b
  }

  /** like startsWith but for multiple options */
  def startsWithAny(k: String*) = k.toList.exists(s => startsWith(s))
  /** skips either of two options, true if it was the first one */
  def skipEither(t: String, f: String): Boolean = {
    if (startsWithS(t)) true else {skipT(f); false}
  }

  /*+ skip all whitespace and comments, return true if newline crossed */
  def trim: Boolean = {
    var newlineSeen = false
    while (!atEnd && (Character.isWhitespace(next) || startsWith("//"))) {
      if (Character.isWhitespace(next)) {
        if (next == '\n') newlineSeen = true
        index += 1
      }
      else {
        while (!atEnd && next != '\n') index += 1
      }
    }
    newlineSeen
  }

  /** the whitespace before the current index contains a newline */
  def newlinesBefore(multiple: Boolean = false): Boolean = {
    var needMultiple = multiple
    var i = index-1
    while (i>0) {
      val c = input(i)
      if (!c.isWhitespace) return false
      if (c == '\n') {
        if (needMultiple) needMultiple = false
        else return true
      }
      i -= 1
    }
    false
  }
  def newlineBefore = newlinesBefore(multiple = false)
  def emptyLineBefore = newlinesBefore(multiple = true)
  def whitespaceBefore: Boolean = {
    index != 0 && Character.isWhitespace(input(index-1))
  }

  /** parses the string s and throws it away */
  def skip(s: String) = {
    if (!startsWith(s, false)) {
      reportError("expected " + s, index, index+1)
    } else {
      index += s.length
    }
  }
  /** [[skip]] s and all following whitespace (i.e. [[trim]] afterwards)*/
  def skipT(s: String) = {skip(s); trim}

  /** check if input left after parsing */
  def parseAll[A](parse: => A) = {
    val a = parse
    if (!atEnd) reportError("expected end of input", index, inputLength)
    a
  }

  /** Parse a sequence of the form {{{a_1 sep ... sep a_n term}}} by applying [[parse]] to all items.
    */
  def parseList[A](parse: => A, sep: String, term: String): List[A] = parseList(parse, Some(sep), Some(term))

  /** Parse a sequence of the form
    * {{{a_1 sep ... sep a_n term}}}
    * by applying `parse` to all items.
    *
    * @param parse The function used to parse all items
    * @param sep The item separator.
    *            If [[None]], parsing will continue until the terminator is found.
    * @param term The list terminator.
    *             If [[None]] or [[Some("")]], parsing will continue until no more separator is found
    *
    * ==WARNING:==
    * If [[sep]] == [[Some("")]] parsing will continue indefinitely
    *
    * @note If [[sep]] and [[term]] are both [[None]], [[parse]] will be called exactly once
    * @note If [[sep]] == [[term]] the parsed sequence cannot be well-formed
    */
  private def parseList[A](parse: => A, sep: Option[String], term: Option[String]): List[A] = {
    trim
    if (term.exists(t => startsWith(t))) return Nil
    var as: List[A] = Nil
    var break = false
    while (!break) {
      trim
      as ::= parse
      trim
      if (sep.exists(t => startsWith(t))) {
        sep.foreach(skip)
      } else if (term.exists(t => startsWith(t))) {
        break = true
      } else if (term.isEmpty) {
        // if no terminator is given, we end if no separator follows
        break = true
      } else if (sep.isDefined) {
        // parse error; will be reported by the caller because no terminator follows
        break = true
      }
      // otherwise: no separator, repeat until terminator found
    }
    as.reverse
  }

  // taking Unicode characters (= Int), which correspond 1 or 2 Java chars in the input
  def parseWhile(p: Unicode.UChar => Boolean) = {
    val start = index
    var continue = true
    while (!atEnd && continue) {
      val c = input.codePointAt(index)
      continue = p(c)
      if (continue) index += Character.charCount(c)
    }
    input.substring(start,index)
  }

  def isNameStart(c: Unicode.UChar) = Character.isLetter(c) || isNameConnector(c)
  def isNameChar(c: Unicode.UChar) = Character.isLetterOrDigit(c) || isNameConnector(c)
  @inline def isNameConnector(c: Unicode.UChar) = c == '_'

  /** Parse a name.
    *
    * Names are alphanumeric, but may not start with a digit.
    * Underscores ("_") are allowed at any position as well.
    */
  def parseName = {
    trim
    if (atEnd || !isNameStart(next)) "" else {
      // identifiers end when the script changes; that allows eg sinα or λx without space
      val script = Unicode.scriptOf(next)
      parseWhile(c => isNameChar(c) && (!Character.isLetter(c) || Unicode.scriptOf(c) == script))
    }
  }
  /** Parse an extended name.
    * Extended names may switch to non-alphanumeric (and back) after an underscore ("_")
    * @todo Extended names are allowed to start with a digit. Is this intentional?
    */
  def parseNameExtended = {
    trim
    var allowNameChars = true
    var allowSpecialChars = false
    parseWhile {c =>
      val good = isNameConnector(c) ||  (allowNameChars && isNameChar(c)) || (allowSpecialChars && !isNameChar(c) && !Character.isWhitespace(c))
      allowSpecialChars = isNameConnector(c) || !isNameChar(c) // special chars may follow _ or other special chars
      allowNameChars = isNameConnector(c) || isNameChar(c) // name chars may follow _ or other name chars
      good
    }
  }
  /** parse a dot (".") separated sequence of names */
  def parsePath: Path = addRef {
    val ns = parseList(parseName, Some("."), None)
    Path(ns)
  }

  import Keywords._

  /** check if a declaration follows */
  // TODO: no good way to differentiate T{s(x) = ...} and T{s(x)}
  def startsWithDeclaration = {
    val backtrackPoint = index
    trim
    val isDecl = allDeclKeywords.exists(k => startsWith(k)) || {
      val n = parseName
      trim
      n.nonEmpty && (nextIs(':') || nextIs('=') || nextIs('#'))
    }
    index = backtrackPoint
    isDecl
  }

  def startsWithUnbracketedArgument = !atEnd &&
    (isNameChar(next) || (whitespaceBefore && Symbols.isOpeningBracketStart(next).isDefined))

  def parseExpressionOrDeclarations(defaultName: String) = {
    trim
    if (atEnd) Nil else if (startsWithDeclaration) parseDeclarations(false)
    else {
      val e = parseExpression(PContext.empty)
      List(ExprDecl(defaultName,LocalContext.empty,Type.unknown(),Some(e), None, Modifiers(false,false)))
    }
  }

  def parseDeclaration(implicit closed: Boolean): Declaration = addRef {
    var mods = Modifiers(closed, false)
    while (startsWithAny(modifiers:_*)) {
      if (startsWithS(openDecl)) mods = mods.copy(closed = false)
      else if (startsWithS(closedDecl)) mods = mods.copy(closed = true)
      else fail("illegal modifier")
    }
    if (startsWithAny(closedModule,openModule)) parseModule
    else if (startsWithAny(include,totalInclude)) parseInclude
    else if (startsWithS(typeDecl)) parseTypeDecl(mods)
    else if (startsWithS(mutableExprDecl)) parseExprDecl(mods.copy(mutable=true))
    else if (startsWithS(exprDecl)) {
      trim
      val n = parseNameExtended
      if (n.isEmpty) fail("name expected")
      parseExprDecl(mods, Some(n))
    }
    else parseExprDecl(mods)
    // else fail("declaration expected")
  }

  def parseDeclarations(implicit closed: Boolean): List[Declaration] = {
    var decls: List[Declaration] = Nil
    var break = false
    while (!break) {
      trim
      if (atEnd || nextIs('}')) {break = true}
      else {
        if (startsWith(",")) skip(",")
        val d = try {
          parseDeclaration
        } catch {
          case Abort() =>
            parseWhile(_ != '}') // skip until a point where we can recover
            return decls.reverse
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
    val dfBegin = index
    skip("{")
    val decls = parseDeclarations(closed)
    trim
    skip("}")
    val df = TheoryValue(decls)
    setRef(df,dfBegin)
    Module(name, closed, df)
  }

  def parseInclude: Include = {
    implicit val ctx = PContext.empty
    val rz = skipEither(totalInclude,include)
    val dom = parseTheory(ctx.copy(terminators = List("=")))
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
    val indexPre = index
    var declarationFound = false
    val name = nameAlreadyParsed getOrElse parseNameExtended
    if (name.isEmpty) fail("name expected")
    val (pcon, tpCont, expCont) = parseArgumentContext()
    var equalOptional = false
    val tp = if (startsWithS(":---", false)) {
      // sugar for declaring an axiom: c:--- F ---->  c: |- Forall F
      declarationFound = true
      val e = parseExpression(pcon.copy(eager = None))
      ProofType(Quantifier(true, null, e).copyFrom(e))
    } else if (startsWithS(":", false)) {
      declarationFound = true
      parseType(pcon.copy(terminators = List("=","#")))
    } else if (startsWith("{", false)) {
      // sugar for declaring methods as f(args) {body} instead of f(args):unit = {body}
      equalOptional = true
      Unit.Type
    } else {
      Type.unknown()
    }
    var vl: Option[Expression] = None
    var nt: Option[Notation] = None
    def parseDef = {
      trim
      if (startsWithS("=", false) || equalOptional) {
        declarationFound = true
        vl = Some(parseExpression(pcon))
      }
    }
    def parseNot = {
      trim
      if (startsWithS("#")) {
        equalOptional = false
        nt = Some(parseNotation)
      }
    }
    // c # ... = ...
    parseNot
    parseDef
    // c = ... # ...
    // TODO this does not work yet because # is parsed as a postfix operator in the definiens
    if (vl.isEmpty && nt.isDefined) parseDef
    if (!declarationFound) {
      fail("declaration of " + name + " ends unexpectedly", indexPre)
    }
    // bind arguments in type and definiens
    val (atp,avl) = expCont match {
      case None => (tp,vl)
      case Some(lc) => (FunType(lc,tp).copyFrom(tp), vl map {v => Lambda(lc,v, true).copyFrom(v)})
    }
    ExprDecl(name, tpCont, atp, avl, nt, mods)
  }

  // type a[X,Y](x:X, y:Y) where X, Y are type variables
  def parseTypeDecl(mods: Modifiers): TypeDecl = {
    val begin = index
    val name = parseName
    val (pcon,tc,ec) = parseArgumentContext()
    val unbounded = Type.unbounded
    setRef(unbounded, begin)  // location of name for the default upper bound
    trim
    val (tp,df) = if (startsWithS("=")) {
      (unbounded,Some(parseType(pcon)))
    } else if (startsWithS("<")) {
      (parseType(pcon), None)
    } else {
      (unbounded, None)
    }
    val jointC = tc append ec.getOrElse(LocalContext.empty)
    TypeDecl(name, jointC, tp, df, mods)
  }

  // @(a,...)(x:A,...)
  def parseArgumentContext() = {
    implicit var pcon = PContext.empty
    trim
    val tc = if (startsWithS("@")) parseTypeContext else LocalContext.empty
    pcon = pcon append tc
    trim
    val ec = if (startsWith("(")) Some(parseBracketedContext) else None
    trim
    ec foreach {a => pcon = pcon append a}
    (pcon,tc,ec)
  }


  /** counts how many extra : a VarDecl has */
  private class ColonCounter {var extras: Int = 0}
  // a variable declaration, possibly using multiple colons (0 for :, 1 for :: etc.)
  def parseMultiVarDecl(mutable: Boolean, nameMandatory: Boolean)(implicit ctxs: PContext): (EVarDecl,Int) = {
    val cc = new ColonCounter
    val vd = parseVarDecl(mutable, nameMandatory, cc)
    (vd,cc.extras)
  }
  // variable declaration with a single :
  def parseVarDecl(mutable: Boolean, nameMandatory: Boolean)(implicit ctxs: PContext): EVarDecl = {
    val (vd,extras) = parseMultiVarDecl(mutable, nameMandatory)
    if (extras > 0) reportError("too many \":\"", vd.loc.from)
    vd
  }
  private def parseVarDecl(mutable: Boolean, nameMandatory: Boolean, colonCounter: ColonCounter)(implicit ctxs: PContext): EVarDecl = addRef {
    val noStatements = ctxs.copy(allowStatement = false)
    val backtrackPoint = index
    val n = parseName
    trim
    if (!nextIs(':') && !nextIs('=') && !nameMandatory && !mutable) {
      // n is not actually a variable name, treat this as anonymous var decl
      index = backtrackPoint
      val tp = parseType(noStatements)
      EVarDecl.anonymous(tp)
    } else {
      val tp = if (nextIs(':')) {
        skip(":")
        while (nextIs(':')) {colonCounter.extras += 1; skip(":")}
        parseType(noStatements.copy(terminators = "=" :: ctxs.terminators))
      } else Type.unknown()
      val df = if (nextIs('=')) {
        skip("=")
        Some(parseExpression(noStatements))
      } else None
      EVarDecl(n, tp, df, mutable)
    }
  }

  def parseContext(namesMandatory: Boolean, endIf: Option[String] = None)(implicit ctxs: PContext): ExprContext = addRef {
    val btp = index
    var vds = parseList(parseMultiVarDecl(false, namesMandatory), Some(","), endIf)
    // conflict between parsing a single name n as "":n or n:???
    // heuristic: only allow the latter if no other variable is named
    if (!namesMandatory && vds.exists(!_._1.anonymous) && vds.exists(vd => vd._1.anonymous && vd._1.tp.isInstanceOf[ClosedRef])) {
      index = btp
      vds = parseList(parseMultiVarDecl(false, true), Some(","), endIf)
    }
    // number of previous (i.e., later since we revert the list) declarations into which a type should be copied
    var previousType: Type = null
    var useMultiType = 0
    val vdsR = Util.reverseMap(vds) {case (vd,i) =>
      if (useMultiType>0) {
        useMultiType -= 1
        if (vd.tp.known || i > 0) {
          reportError("omitted type expected due to subsequent ::", vd.loc.from)
          vd
        } else {
          vd.copy(tp = previousType)
        }
      } else {
        previousType = vd.tp
        useMultiType = i
        vd
      }
    }
    if (useMultiType > 0) {
      reportError("declaration with omitted type expected due to subsequent ::", vds.head._1.loc.from)
    }
    // no need to call make because we've already reversed the list
    ExprContext(vdsR)
  }

  def parseBracketedContext(implicit ctxs: PContext): ExprContext = {
    trim
    if (startsWithS("(")) {
      val c = parseContext(false, Some(")"))(ctxs.copy(terminators = List(")")))
      skip(")")
      c
    } else {
      ExprContext.empty
    }
  }

  def parseTypeContext() = addRef {
    trim
    val ns = if (startsWithS("(")) {
      val r = parseList(parseName, ",", ")")
      trim
      skip(")")
      r
    } else {
      List(parseName)
    }
    LocalContext.make(ns.map(TVarDecl(_,None)))
  }

  def parseTypeArgs(implicit ctxs: PContext) = {
    trim
    val ctxsT = ctxs.copy(inType = true, eager = Some(true), terminators = List(",",")"))
    if (startsWithS("(")) {
      val r = parseList(parseType(ctxsT), ",", ")")
      trim
      skip(")")
      r
    } else {
      List(parseType(ctxs.copy(eager = Some(false))))
    }
  }

  def parseNotation = {
    val fix = if (startsWithS(Keywords.nullfix)) {
      Nullfix
    } else if (startsWithS(infix)) {
      Infix
    } else if (startsWithS(prefix)) {
      Prefix
    } else if (startsWithS(postfix)) {
      Postfix
    } else if (startsWithS(circumfix)) {
      Circumfix
    } else if (startsWithS(applyfix)) {
      Applyfix
    } else if (startsWithS(bindfix)) {
      Bindfix
    } else {
      fail("fixity expected")
    }
    val sym = parseWhile(! Character.isWhitespace(_))
    Notation(fix, sym)
  }

  def parseExpressions(open: String, close: String)(implicit ctxs: PContext) = {
    val ctxsI = ctxs.copy(eager = Some(true), inType = false, terminators = List(",", close))
    skip(open)
    val es = parseList(parseExpression(ctxsI), ",", close)
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
    val e = parseExpression(ctxs.copy(eager = Some(true), terminators = List(")")))
    skip(")")
    e
  }
  // needed because addRef does not work with return-statements
  private def parseExpressionInner(implicit ctxs: PContext): Expression = {
    // val upcoming = input.substring(index,Math.min(index+10,inputLength)) // for debugging
    val veryEagerly = ctxs.copy(eager = Some(true))
    val eagerly = ctxs.copy(eager = None)
    val lazily = ctxs.copy(eager = Some(false))
    val allowS = lazily.allowStatement
    val doAllowS = ctxs.copy(allowStatement = true)
    val doNotAllowS = ctxs.copy(allowStatement = false)
    val allExpBeginAt = index
    // seen.reverse = (e,o)::... represents having shifted "e o ..."; exp is the current expression, the RHS of the last infix
    var seen: List[(Expression,PseudoOperator)] = Nil
    var exp: Expression = null
    var shiftInfixes = true
    while (shiftInfixes) {
      trim
      val expBeginAt = index
      var expBracketed = false
      exp = if (nextIs('.')) {
        skip(".")
        if (!atEnd && isNameChar(next)) {
          // .id is OpenRef
          OpenRef(parsePath)
        } else {
          // . is this, .. is parent and so on
          var l = 1 // starting a 1, because we skipped a dot already
          while (nextIs('.')) {l += 1; skip(".")}
          // .a is this.a, ..a is parent.a, and so on; thus: if .id follows, we keep the last .
          if (!atEnd && isNameChar(next)) index-=1
          This(l)
        }
      } else if (startsWithS("§{")) {
        val begin = index
        val ds = parseDeclarations(true)
        trim
        skip("}")
        val thy = setRef(Theory(ds),begin)
        if (ctxs.inType) UndefinedValue(ClassType(thy)) else Instance(thy)
      } else if (!ctxs.inType && startsWithS("{")) {
        var cs: List[Expression] = Nil
        var ctxL = ctxs.copy(allowStatement = true, terminators = List(";", "}"))
        trim
        while (!startsWithS("}")) {
          val c = parseExpression(ctxL)
          cs ::= c
          c match {
            case vd: EVarDecl => ctxL = ctxL.append(vd)
            case _ =>
          }
          trim
          if (startsWith(";")) skip(";")
        }
        Block(cs.reverse)
      } else if (!ctxs.inType && startsWithS(Keywords.mutableVarDecl)) {
        trim
        parseVarDecl(true, true)
      } else if (!ctxs.inType && startsWithS(Keywords.varDecl)) {
        trim
        parseVarDecl(false,true)
      } else if (!ctxs.inType && startsWithAny("exists","forall")) {
        val univ = skipEither("forall", "exists")
        val vars = parseContext(true, Some("."))(ctxs.copy(terminators = List(".")))
        skipT(".")
        val body = parseExpression(eagerly)
        Quantifier(univ,vars,body)
      } else if (!ctxs.inType && startsWithS("Forall")) {
        val body = parseExpression(eagerly)
        Quantifier(true,null,body) // universal closure: Forall e --> forall ???. e
      } else if (!ctxs.inType && startsWithS("ASSERT")) {
        trim
        val es = parseExpressions("(", ")")
        val (test, expected) = if (es.length == 1) (es.head, BoolValue(true))
        else if (es.length == 2) (es(0),es(1))
        else {
          reportError("only 2 arguments allowed", es(2))
          (es(0),es(1))
        }
        Assert(test,Type.unknown(),expected)
      } else if (!ctxs.inType && allowS && startsWithS("while")) {
        val c = parseBracketedExpression
        val b = parseExpression(doAllowS)
        While(c,b)
      } else if (!ctxs.inType && allowS && startsWithS("for")) {
        skipT("(")
        val v = parseName
        trim
        skipT("in")
        val r = parseExpression(ctxs.copy(terminators = List(")")))
        skipT(")")
        val b = parseExpression(doAllowS.append(EVarDecl(v,Type.unknown())))
        For(EVarDecl(v,Type.unknown()),r,b)
      } else if (!ctxs.inType && startsWithS("if")) {
        val c = parseBracketedExpression
        val th = parseExpression(ctxs.copy(terminators = "else" :: ctxs.terminators))
        trim
        val el = if (startsWithS("else")) {
          Some(parseExpression)
        } else {
          if (!allowS) reportError("else branch expected", index)
          None
        }
        IfThenElse(c,th,el)
      } else if (!ctxs.inType && allowS && startsWithAny("return","throw")) {
        val thrw = skipEither("throw","return")
        val r = parseExpression(eagerly)
        Return(r,thrw)
      } else if (!ctxs.inType && startsWithS("\"")) {
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
      } else if (!ctxs.inType && startsWithS("true")) {
        BoolValue(true)
      } else if (!ctxs.inType && startsWithS("false")) {
        BoolValue(false)
      } else if (!ctxs.inType && !atEnd && Parser.digits.contains(next)) {
        val begin = index
        var seenDot = false
        while (!atEnd && (Parser.digits.contains(next) || (!seenDot && next == '.'))) {
          if (next == '.') seenDot = true
          index += 1
        }
        val s = input.substring(begin,index)
        if (seenDot)
          FloatValue(s.toFloat)
        else
         IntValue(s.toInt)
      } else if (startsWithS("???")) {
        UndefinedValue(Type.unknown())
      } else if (!ctxs.inType && startsWithS("`")) {
        if (ctxs.contexts.length <= 1) reportError("eval outside quotation", index-1, inputLength)
        val e = parseExpression(ctxs.pop().copy(terminators = List("`")))
        skip("`")
        Eval(e)
      } else if (startsWith("(")) {
        /* options: inType; -> follows; brackets contain VarDecls
             (type): bracketed type, parsed as (_:type)
             (context): unit type, bracketed type, product type
             (type) -> type: bracketed domain in function type,
             (context) -> type: function type
             (exp): unit value, bracketed expression, tuple
             (context): not allowed, var decls parsed as tuple components
             (exp) -> exp: match case
             (context) -> exp: lambda
         */
        if (ctxs.inType) {
          val comps = parseBracketedContext // allows for (A,...)
          val tp = comps.variables match {
            case List(vd) if vd.anonymous =>
              // (type)
              vd.tp
            case _ =>
              trim
              if (startsWithS("->")) {
                val r = parseType
                // (context) -> type
                FunType(comps, r)
              } else {
                // (context)
                ProdType(comps)
              }
          }
          UndefinedValue(tp)
        } else {
          val es = parseExpressions("(", ")")
          val tuple = setRef(TupleGeneral(es), expBeginAt)
          trim
          if (!ctxs.terminators.contains("->") && startsWith("->")) {
            val vdOs = es.map(expToVarDecl)
            if (vdOs.forall(_.isDefined)) {
              val ins = ExprContext.make(vdOs.map(_.get)).copyFrom(tuple)
              skip("->")
              val bd = parseExpression(doAllowS)
              Lambda(ins,bd,false)
            } else {
              tuple
            }
          } else {
            expBracketed = true
            tuple
          }
        }
      } else if (startsWith("[") || startsWithAny(CollectionKind.allKeywords :_*)) {
          val kind = if (startsWith("[")) CollectionKind.List
          else CollectionKind.allKinds.find(k => startsWithS(k._1)).get._2
          if (ctxs.inType) {
            skip("[")
            val tp = parseType(ctxs.copy(eager = Some(true), terminators = List("]")))
            skip("]")
            UndefinedValue(CollectionType(tp,kind))
          } else {
            val es = parseExpressions("[","]")
            CollectionValue(es, kind)
          }
      } else if (ctxs.inType && startsWithS("|-")) {
        // will be turned into ProofType by parseType
        val ctxF = eagerly.copy(inType = false, allowStatement = false, terminators = "->" :: ctxs.terminators)
        val f = parseExpression(ctxF)
        UndefinedValue(ProofType(f))
      } else if (ctxs.inType && startsWith("_") && nextAfter(1).exists(!isNameChar(_))) {
        skip("_")
        UndefinedValue(Type.unknown())
      } else if (ctxs.inType && startsWithS("int")) {
        trim
        val tp = if (startsWithS("[")) {
          trim
          val lower = if (nextIs(';')) null else parseExpression(ctxs.copy(inType = false, terminators = List(";")))
          trim
          skipT(";")
          val upper = if (nextIs(']')) null else parseExpression(ctxs.copy(inType = false, terminators = List("]")))
          trim
          skip("]")
          IntervalType(Option(lower), Option(upper))
        } else {
          NumberType.Int
        }
        UndefinedValue(tp)
      } else {
        val opO = if (ctxs.inType) None else parseOperator
        opO match {
          case Some(op) =>
            // initial operator
            if (op.opening) {
              val es = parseExpressions("", Symbols.makeClosingBracket(op.symbol))
              val oes = op.toApplication(Circumfix, es)
              if (startsWithUnbracketedArgument) {
                // a circumfix can take one extra argument without whitespace
                setRef(oes, op.loc.from)
                val a = parseExpression(lazily)
                Application(oes, List(a))
              } else
                oes
            } else if (op.closing) {
              fail("unexpected closing bracket", at = op.loc.from)
            } else {
              // multiple resolutions for op
              @inline def nullfix() = op.withFixity(Nullfix).toExpression
              @inline def prefix() = {
                val e = parseExpression(lazily)
                op.toApplication(Prefix, List(e))
              }
              @inline def bindfix() = parseBinding(op.withFixity(Bindfix).toExpression)
              if (atEndOfLine || startsWithTerminator) {
                nullfix()
              } else if (startsWithBinding) {
                bindfix()
              } else if (op.attachRight || op.unspaced) {
                prefix()
              } else if (ctxs.eager contains false) {
                nullfix()
              } else {
                // peek at the next operator (if any)
                trim
                val afterOp = index
                val op2O = parseOperator
                index = afterOp
                op2O match {
                  case Some(op2) =>
                    if (op2.opening) prefix()
                    else if (op2.closing) nullfix()
                    else if (op2.symmetric) {
                      // op2 is infix whose left argument is op
                      nullfix()
                    } else {
                      prefix()
                    }
                  case None => prefix()
                }
              }
            }
          case None =>
            // symbol/variable/module reference
            val n = parseName
            if (n.isEmpty) fail("name expected")
            trim
            if (startsWith(":") && !nextAfter(1).exists(Symbols.isOperatorChar)) {
              // variable declaration
              skip(":")
              val tp = parseType(doNotAllowS)
              EVarDecl(n, tp)
            } else if (n == "_") {
              EVarDecl.anonymous(Type.unknown()) // anonymous variable
            } else if (ctxs.declares(n)) {
              VarRef(n) // reference to bound variable
            } else {
              ClosedRef(n) // default for names that must be resolved during type-checking
            }
        }
      } // end exp =
      setRef(exp, expBeginAt)
      trim

      // ******** repeated check for and apply post-operators by modifying exp
      /* state
          seen: shifted expressions and infixes
          exp: current expression
          and the Booleans below
       */
      var takePostops = true // termination condition
      // available state transitions
      def stopPostops() = {
        takePostops = false
      }
      // updates exp after parsing a postop (without changing the shifted infixes)
      def modifyExp(e: Expression) = {
        exp = e
        setRef(exp,expBeginAt)
      }
      def modifyExpByApplying(es: List[Expression]) = {
        val expM = if (!ctxs.inType) Application(exp,es) else {
          val tp = expressionToType(exp).getOrElse(fail("not a type that can take arguments"))
          val tpes = tp match {
            case MaybeAppliedRef(r,tps,Nil) => MaybeAppliedRef(r,tps,es)
            case _ => fail("type cannot take multiple argument lists")
          }
          UndefinedValue(tpes)
        }
        modifyExp(expM)
      }
      // reduce infixes and stop trying postops
      def reduceInfixes() = {
        exp = disambiguateInfixOperators(seen.reverse,exp)
        setRef(exp,allExpBeginAt)
        seen = Nil
        takePostops = false
        shiftInfixes = false
      }
      // shift exp with an infix operator; exp set to null to indicate shifting
      def shift(op: PseudoOperator) = {
        seen ::= (exp, op)
        exp = null
        stopPostops()
      }
      // non-bracket postops that can still be applied after a postifx operator and therefore prevent infix operators
      val weakBindingPostops = List("catch", "match", "->", ".")
      while (takePostops) {
        trim
        // properties of exp that are used to determine whether certain postifes are available
        // unitary expressions can take a tight-binding postfix operator
        val expIsUnitary = exp match {
          case _ if expBracketed => true
          case _: BaseValue | _: Ref | _: AppliedRef | _: This | _: OwnedObject | _: Tuple | _: CollectionValue | _: Instance
               | _: Block | _: OwnedExpr => true
          case Application(BaseOperator(pop: PseudoOperator,_), _) =>
              val f = pop.fixity
              f != Infix && f != Prefix
          case _: Application => true
          case _ => false
        }

        // identifiers can take parameters
        def asRef(e: Expression): Option[Ref] = e match {
          case OwnedExpr(e, _, ClosedRef(n)) => asRef(e).map {
            case OpenRef(p) => OpenRef(p / n)
            case ClosedRef(m) => OpenRef(Path(m) / n)
            case VarRef(m) => OpenRef(Path(m) / n)
          }
          case r: Ref => Some(r)
          case _ => None
        }

        val expIsRef = asRef(exp)
        // Block can return a value, so not a statement
        val expIsStatement = exp match {
          case _: Assign | _: EVarDecl | _: While | _: For | _: Return => true
          case _ => false
        }
        val expIsType = exp match {
          case UndefinedValue(tp) => !tp.isInstanceOf[UnknownType]
          case _ => false
        }
        val startOfLine = newlineBefore
        // now a large if-else that checks for what follows and calls the state transitions above
        if (endOfTermPassed) {
          stopPostops()
        } else if (nextIs('.') && nextAfter(1).exists(isNameStart) && expIsUnitary) {
          // we check this before the terminators so that "." is no terminator if identifier follows without whitespace
          skip(".")
          val nB = index
          val n = parseName
          // if (n.isEmpty) fail("identifier expected")
          val owned = setRef(ClosedRef(n),nB)
          val expM = if (ctxs.inType) UndefinedValue(OwnedType(exp,null,owned)) else OwnedExpr(exp,null,owned)
          modifyExp(expM)
        } else if (startsWithTerminator) {
          // the term is done
          reduceInfixes()
        } else if (!startOfLine && expIsRef.isDefined && startsWithS("@")) {
          val r = expIsRef.get
          val tps = parseTypeArgs
          modifyExp(AppliedRef(r,tps,Nil))
        } else if (!startOfLine && expIsUnitary && startsWithS("(")) {
          val es = parseExpressions("",")")
          modifyExpByApplying(es)
        } else if (!expIsType && startsWith("[") && expIsUnitary && !startOfLine) {
          skip("[")
          val e = parseExpression(ctxs.copy(terminators = List("]")))
          skip("]")
          modifyExp(ListElem(exp,e))
        } else if (expIsUnitary && startsWithS("{")) {
          // conflict between M{decls} and exp{exp}
          // check if there was a Ref before
          expIsRef match {
            case Some(r) if startsWithDeclaration || nextIs('}') =>
              // p{decls}
              val incl = setRef(Include(r), expBeginAt)
              val indexPre = index
              val ds = parseDeclarations(true)
              val sds = ds.flatMap {
                case sd: SymbolDeclaration => List(sd)
                case _ => reportError("symbol declaration expected", indexPre); Nil
              }
              val thy = setRef(Theory(incl::sds), incl.loc.from)
              val expM = if (ctxs.inType) UndefinedValue(ClassType(thy)) else Instance(thy)
              modifyExp(expM)
            case _ =>
              // in e{q}, q is a closed expression in a different theory
              val ctxsI = ctxs.push().copy(terminators = List("}"))
              val expM = if (ctxs.inType) {
                val t = parseType(ctxsI)
                UndefinedValue(OwnedType(exp,null,t))
              } else {
                val e = parseExpression(ctxsI)
                OwnedExpr(exp, null, e)
              }
              modifyExp(expM)
          }
          skip("}")
        } else if (expIsUnitary && startsWithS("°")) {
          reduceInfixes()
          // function application with Andrews' dot
          val a = parseExpression(eagerly.copy(inType = false))
          modifyExpByApplying(List(a))
        } else if (!ctxs.inType && startsWith("=")) {
          reduceInfixes()
          skip("=")
          val df = parseExpression
          modifyExp(Assign(exp, df))
        } else if (startsWithS("->")) {
          reduceInfixes()
          // if the LHS of -> had been bracketed, this would already have been parsed above
          if (ctxs.inType) {
            val lhs = expressionToType(exp).getOrElse(UnivType(exp,null))
            val ins = ExprContext.make(List(EVarDecl.anonymous(lhs))).copyFrom(lhs)
            val rhs = parseType
            val ftp = UndefinedValue(FunType(ins, rhs))
            modifyExp(ftp)
          } else {
            val bd = parseExpression
            val expM = expToVarDecl(exp) match {
              case Some(vd) =>
                Lambda(ExprContext.make(List(vd)), bd, false)
              case None =>
                reportError("variable declaration expected", exp)
                Lambda(ExprContext.empty, bd, false)
            }
            modifyExp(expM)
          }
        } else if (ctxs.inType && startsWithS("?")) {
          val tp = expressionToType(exp).getOrElse(UnivType(exp,null))
          val tpM = UndefinedValue(CollectionKind.Option(tp))
          modifyExp(tpM)
        } else if (!ctxs.inType && startsWithAny("match","catch")) {
          reduceInfixes()
          val handle = skipEither("catch", "match")
          skip("{")
          val cs = parseList(parseMatchCase, None, Some("}"))
          skip("}")
          modifyExp(Match(exp, cs, handle))
        } else if (!ctxs.eager.contains(false) && startsWithUnbracketedArgument && expIsUnitary) {
          // switch to whitespace-application
          val btp = index
          if (startsWithBinding) {
            val bexp = parseBinding(exp)
            modifyExp(bexp)
          } else {
            trim
            // if we currently very eager, we take arguments also from the next line
            // continue on the next line eagerly, on the same line lazily
            while (!endOfTermPassed && startsWithUnbracketedArgument) {
              val conA = if (newlineBefore) eagerly else lazily
              val a = parseExpression(conA.copy(inType = false))
              // multiple arguments are curried to match the curried style of writing functions
              modifyExpByApplying(List(a))
              trim
            }
          }
        } else if (!expIsType) {
          // lookahead and collect all following operators, possibly ending in an open bracket
          var opsR: List[UnfixedOperator] = Nil
          var openBracket: Option[UnfixedOperator] = None
          var parseOps = true
          var termEnds = false
          val beforeOps = index
          while (parseOps) {
            trim
            if (endOfTermPassed || startsWithTerminator || startsWithAny(weakBindingPostops:_*)) {
              parseOps = false; termEnds = true
            }
            else parseOperator match {
              case Some(o) if o.opening => parseOps = false; openBracket = Some(o)
              case Some(o) if o.closing => parseOps = false; termEnds = true
              case Some(o) => opsR ::= o
              case None => parseOps = false; termEnds = false
            }
          }
          index = beforeOps // index will be moved manually below when operators are consumed
          val ops = opsR.reverse
          if (ops.nonEmpty || openBracket.isDefined) {
            // now decide which opeartors we consume and how
            // longest operator is infix; if tied, taking the first one prefers prefix over postfix
            val (postfixes, infixO, applyO) = if (ops.isEmpty) {
              // open bracket by itself: applyfix
              (Nil, None, openBracket)
            } else {
              val (opM, i) = ops.zipWithIndex.maxBy(_._1.precedence)
              val lastOpIsLongest = i == ops.length - 1
              if (!expIsUnitary && ops.nonEmpty) {
                // non-unitary expression cannot take applyfix or postfix
                (Nil, Some(ops.head), None)
              } else if (lastOpIsLongest) {
                // special case if the last operator should be outermost
                if (termEnds) {
                  (ops, None, None) // openBracket.isEmpty
                } else {
                  openBracket match {
                    case None =>
                      // postfixes until opM
                      (ops.init, Some(opM), None)
                    case Some(ob) =>
                      // postfix+applyfix vs. infix+circumfix: decide for the former
                      (ops.init, Some(opM), None)
                  }
                }
              } else {
                // postfixes until opM, then reparse the rest later
                (ops.take(i), Some(opM), None)
              }
            }
            postfixes.foreach {pf =>
              index = pf.loc.to
              modifyExp(pf.toApplication(Postfix, List(exp)))
            }
            // applyO and infixO are not both defined
            applyO.foreach {ob =>
              index = ob.loc.to
              // the special cases ([{ are reparsed above
              if (ob.symbol != "(" && ob.symbol != "[" && ob.symbol != "{") {
                val es = parseExpressions("", Symbols.makeClosingBracket(ob.symbol))
                modifyExp(ob.toApplication(Applyfix, exp :: es))
              }
            }
            infixO.foreach {ifo =>
              index = ifo.loc.to
              shift(ifo.withFixity(Infix))
            }
            // remaining operators will be parsed again, usually as prefixes
          } else {
            stopPostops()
          }
        } else {
          stopPostops()
        } // end if
      } // end while that applies postops
      // no more postops and no infixes: finalize expression
      if (exp != null) {
        // stop shifting
        reduceInfixes()
        shiftInfixes = false
      }
      // otherwise, the current expression was shifted and we continue
    } // end while that shifts infix ops
    // seen.isEmpty here
    exp
  }

  def parseMatchCase(implicit ctxs: PContext) = addRef {
    val e = parseExpression(ctxs.copy(terminators = List("->")))
    trim
    skip("->")
    val b = parseExpression
    MatchCase(null, e, b)
  }

  private def expToVarDecl(e: Expression): Option[EVarDecl] = {
    val vdO = e match {
      case vd: EVarDecl if !vd.mutable => vd
      case ClosedRef(n) => EVarDecl(n, Type.unknown()).copyFrom(e)
      case VarRef(n) => EVarDecl(n, Type.unknown()).copyFrom(e) // shadowing
      case e => null
    }
    Option(vdO)
  }

  // tests for "x,...,x:", "x,...,x. "
  def startsWithBinding(implicit ctxs: PContext): Boolean = {
    // check if we're already parsing a binding
    if (ctxs.terminators.contains(".")) return false
    val btp = index
    trim
    val vr = parseName
    trim
    val r = vr.nonEmpty && (
      if (startsWithS(",")) startsWithBinding
      else startsWith(":") || (startsWith(".") && nextAfter(1).exists(Character.isWhitespace))
      )
    index = btp
    r
  }

  def endOfTermPassed(implicit ctxs: PContext) = atEnd || (ctxs.eager match {
    case Some(false) => whitespaceBefore
    case None => newlineBefore
    case Some(true) => emptyLineBefore
  })

  def startsWithTerminator(implicit ctxs: PContext) = {
    startsWithAny(ctxs.terminators:_*)
  }

  // binder ctx. body
  def parseBinding(binder: Expression)(implicit ctxs: PContext) = {
    val vars = parseContext(true, Some("."))(ctxs.copy(terminators = List(".")))
    trim
    skipT(".")
    val body = parseExpression(ctxs.copy(eager = None)) // binder scopes till ends of line
    val arg = Lambda(vars, body, false)
    arg.loc = vars.loc extendTo body.loc
    Application(binder, List(arg))
  }

  // parses an unfixed operator
  // TODO handle _
  def parseOperator: Option[UnfixedOperator] = {
    trim
    val start = index
    if (atEnd) {
      None
    } else if (Symbols.isOpeningBracketStart(next).isDefined) {
      val op = parseNext + parseWhile(Symbols.isBracketChar)
      Some(unfixedOperator(op, start, opening = true))
    } else if (Symbols.isClosingBracketStart(next).isDefined) {
      val op = parseNext + parseWhile(Symbols.isBracketChar)
      Some(unfixedOperator(op, start, closing = true))
    } else if (Symbols.isSingleOpStart(next)) {
      val op = parseNext + parseWhile(Symbols.isSingleOpChar)
      Some(unfixedOperator(op, start))
    } else if (Symbols.isMultiOpStart(next)) {
      val op = parseNext + parseWhile(Symbols.isMultiOpChar)
      Some(unfixedOperator(op, start))
    } else {
      None
    }
  }
  private def unfixedOperator(symbol: String, startIndex: Int, opening: Boolean = false, closing: Boolean = false) = {
    val endIndex = startIndex + symbol.length
    val spaceBefore = {
      var i = 0
      while (startIndex-1-i >= 0 && input(startIndex-1-i) == ' ') i+=1
      i
    }
    val spaceAfter = {
      var i = 0
      while (endIndex+i<inputLength && input(endIndex+i) == ' ') i+=1
      i
    }
    val loc = makeRef(startIndex, endIndex)
    UnfixedOperator(symbol, loc, spaceBefore, spaceAfter, opening, closing)
  }
  // a shift-reduce parser of e1 o1 ... en on last, using space counts for precedence
  def disambiguateInfixOperators(eos: List[(Expression,PseudoOperator)], lastExp: Expression): Expression = {
    /** Precedence of an operator occurrence: number of spaces on the tighter side.
     *  For a symmetric infix operator (sb == sa) this is sb (== sa).
     *  For an asymmetric occurrence we warn and use the minimum (tighter side wins).
     *  Fewer spaces = higher precedence (binds more tightly).
     *  We negate so that higher precedence = larger integer for the shift-reduce comparisons.
     */
    @inline def precedence(o: PseudoOperator): Int = {
      o.precedence
    }
    // invariant: eos last = shifted rest last
    var shifted: List[(Expression, PseudoOperator)] = Nil
    var rest = eos
    var last = lastExp
    // shift: shifted.reverse | hd tl last ---> shifted hd | tl last
    @inline def shift = {
      shifted ::= rest.head
      rest = rest.tail
    }
    // before (a1 o) ... (an o) | after   ---> before (args e o) | after
    @inline def reduce(o: PseudoOperator, e: Expression) = {
      var args = List(e)
      while (shifted.nonEmpty && shifted.head._2.symbol == o.symbol) {
        args ::= shifted.head._1
        shifted = shifted.tail
      }
      Application(o.toExpression,args).withLocation(args.head.loc.extendTo(last.loc))
    }
    while (shifted.nonEmpty || rest.nonEmpty) {
      rest match {
        case Nil =>
          // reduce on the right
          val (_,o) = shifted.head
          last = reduce(o,last)
        case (e2,o2) :: tl =>
          if (shifted.isEmpty) {
            shift
          } else {
            val (e1,o1) = shifted.head
            val p1 = precedence(o1)
            val p2 = precedence(o2)
            if (o1 == o2) {
              // same operator: collect for n-ary application
              shift
            } else if (p1 <= p2) {
              // o1 binds at least as tightly as o2: reduce o1 first
              val o1Applied = reduce(o1,e2)
              shifted ::= (o1Applied,o2)
              rest = tl
            } else {
              // o2 binds more tightly: shift
              shift
            }
          }
      }
    }
    last
  }

  // We reuse expression parsing for 3 reasons:
  // - reuse the code for parsing (applied) references
  // - owned type starts with an expression
  // - expr-to-type coercion allows expressions in type-positions
  // The expression parser uses UndefinedValue(tp) to represent a type and handles all type parsing along the way.
  def parseType(implicit ctxs: PContext): Type = {
    val exp = parseExpression(ctxs.copy(inType = true))
    val tp = expressionToType(exp).getOrElse {
      reportError("type expected", from = exp.loc.from)
      AnyType
    }
    tp.copyFrom(exp)
  }
  private def expressionToType(exp: Expression): Option[Type] = exp match {
    case UndefinedValue(t) => Some(t)
    case exp: ClosedRef =>
      val t = exp.name match {
        case "nat" => NumberType.Nat
        case "int" => NumberType.Int
        case "rat" => NumberType.Rat
        case "comp" => NumberType.RatComp
        case "float" => NumberType.Float
        case "string" => StringType
        case "bool" => BoolType
        case "empty" => EmptyType
        case "exn" => ExceptionType
        case "any" => AnyType
        case _ => exp
      }
      Some(t)
    case r: Ref => Some(r)
    case r: AppliedRef => Some(r)
    case Application(MaybeAppliedRef(r,tpargs,Nil), es) => Some(MaybeAppliedRef(r,tpargs,es))
    // Any other expression, we coerce into a type.
    // This coercion should happen during type-checking (and it does for Refs and OwnedType(_,_,Ref)),
    // but because it changes Scala-type, we have to do it here already.
    case _: Application | _: Projection | _: ListElem => Some(UnivType(exp, null))
    case _ => None
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
  val openDecl = "open"
  val closedDecl = "closed"
  val modifiers = List(openDecl,closedDecl)
  val allDeclKeywords = List(openModule,closedModule,include,totalInclude,mutableExprDecl,typeDecl):::modifiers
  val infix = "infix"
  val prefix = "prefix"
  val postfix = "postfix"
  val circumfix = "circumfix"
  val applyfix = "applyfix"
  val bindfix = "bindfix"
  val nullfix = "nullfix"
  val fixities = List(nullfix, infix, prefix, circumfix, applyfix, bindfix)
}

