package info.kwarc.p

import SyntaxFragment.matchC

import java.awt.event.FocusEvent.Cause
import scala.scalajs.js.|

class Checker(errorHandler: ErrorHandler) {
  private val debug = false

  case class Error(cause: SyntaxFragment,msg: String) extends SError(cause.loc, msg + " while checking " + cause.toString)
  case class Abort() extends Exception
  private def fail(m: String)(implicit cause: SyntaxFragment) = {
    reportError(m)
    throw Abort()
  }
  def reportError(msg: String)(implicit cause: SyntaxFragment) = {
    val e = Error(cause,msg)
    errorHandler(e)
  }
  @inline
  def recoverWith[A](recover: A)(code: => A): A = try {code} catch {
    case Abort() => recover
    case ASTError(m) =>
      val sf = recover match {
        case s: SyntaxFragment => s
        case (s: SyntaxFragment,_) => s // only needed for inferExpression
        case _ => throw IError("unknown result type")
      }
      reportError(m)(sf); recover
  }

  private def expected(exp: SyntaxFragment, found: SyntaxFragment): String = expected(exp.toString, found.toString)
  private def expected(exp: String, found: String): String = s"expected $exp; found $found"

  def checkVocabulary(gc: GlobalContext, voc: Vocabulary, keepFull: Boolean)(implicit cause: SyntaxFragment) = {
    voc.decls.foreach {d => d.global = true}
    val dsC = flattenCheckDeclarations(gc, voc.decls, alsoCheck=true, keepFull)
    Vocabulary(dsC).copyFrom(voc)
  }

  def checkProgram(p: Program): Program = matchC(p) {
    case Program(voc,mn) =>
      val gc = GlobalContext("")
      val vocC = checkVocabulary(gc, voc, true)(p)
      val gcC = GlobalContext(vocC)
      val mnC = checkExpression(gcC,mn,AnyType)
      Program(vocC, mnC).copyFrom(p)
  }

  def checkDeclaration(gc: GlobalContext, decl: Declaration): Declaration = recoverWith(decl) {
    if (debug) println("checking: " + decl)
    implicit val cause = decl
    val declC = decl match {
      case m:Module =>
        // checking will try to merge declarations of the same name, so no uniqueness check needed
        val envM = gc.add(m.copy(decls = Nil).copyFrom(m)).enter(m)
        if (!m.closed) {
          m.decls.foreach {_.global = true}
        }
        val declsC = flattenCheckDeclarations(envM, m.decls, true, true)
        m.copy(decls = declsC)
        // TODO instance creation may occur before or while a theory is checked - needs 2-phase approach
      case id: Include =>
        if (id.dom != null) {
          val domC = checkTheoryPath(gc, id.dom)(id)
          // TODO: what about includes of open theories
          val dfOC = id.dfO map {d => checkExpression(gc,d,ClassType(PhysicalTheory(domC)))}
          Include(domC,dfOC,id.realize)
        } else id.dfO match {
          case None => fail("untyped include")
          case Some(df) =>
            // infer domain from definiens
            val (dfC,dfI) = inferExpression(gc,df)(true)
            PurityChecker(gc,dfC)
            dfI match {
              case ClassType(PhysicalTheory(p)) =>
                Include(p, Some(dfC), id.realize)
              case _ => fail("domain not an atomic theory")
            }
        }
      case sd: SymbolDeclaration =>
        checkSymbolDeclaration(gc, sd)
        // purity checks?
    }
    declC.copyFrom(decl)
  }

  private case class FlattenInput(decls: List[Declaration], alsoCheck: Boolean, alsoTranslate: Option[Include]) {
    def tail = copy(decls = decls.tail)
  }
  /** checking and flattening a list of declarations
      - symbol declarations: keep, possibly merge/clash with existing declaration
      - include T [=m]: keep, possibly merge/clash,
        then also add body of T, recursively addpossibly changing all expressions e to m.e
        this causes an exponential blow-up, but that is acceptable because
        - unrefined declarations are not copied
        - refinements by defined includes need a shallow copy of the declaration
     Any two declarations for the same name get merged as follows:
     - A subsumed declarations is marked and removed at the end.
     - If a new declaration has to be generated, it is added and both refinees are marked as subsumed.
     - Subsuming declarations are marked as well.
     - Declarations are marked to retain the original list.
     keepFull determines what is returned: all non-subsumed declarations or only the subsuming ones and includes
    */
  private def flattenCheckDeclarations(gc: GlobalContext, decls: List[Declaration], alsoCheck: Boolean, keepFull: Boolean)
                                      (implicit cause: SyntaxFragment): List[Declaration] = {
    /* a FIFO queue of lists of declarations that must be flattened
     * Later on included lists of declarations will be prefixed with that flag negated and the definiens of the include.
     * It would be equivalent to keep a List[Declaration] instead of what is essentially a list of lists of declarations
     * if the former always holds the concatenation of the latter.
     * But our implementation is more efficient because it avoids that copying lists.
     */
    // initially, we need to flatten the original list, which must be checked but not translated
    var todo = List(FlattenInput(decls,alsoCheck,None))
    val numPriorDecls = gc.parentDecls.length // new declarations are appended to these
    var gcC = gc // will change as we process declarations
    // adds a declaration to the result, possibly merging with an existing one
    // returns true if added (redundant otherwise)
    def add(d: Declaration, current: FlattenInput): Boolean = {
      val dT = current.alsoTranslate match {
        case None => d
        case Some(incl) => incl.dfO match {
          case None => d
          case Some(df) => OwnerSubstitutor(df,incl.theory,d)
        }
      }
      val old = gcC
      val existing = gcC.parentDecls.view.map {e =>
        (e,Declaration.compare(e,dT))
      }.find {case (e,c) => c != Declaration.Independent}
      existing match {
        case None =>
          if (debug) println("new declaration: " + dT)
          gcC = gcC.add(dT)
        case Some((e,r)) => r match {
          case Declaration.Identical =>
            // new declaration is copy: nothing to do
            if (debug) println("duplicate declaration: " + dT)
          case Declaration.Subsumes =>
            if (debug) println("subsumed declaration: " + dT)
            // new declaration is redundant: nothing to do but remember
            e.subsuming = true
          case Declaration.SubsumedBy =>
            // old declaration is redundant: mark it for later removal
            e.subsumed = true
            dT.subsuming = true
            if (debug) println("subsuming declaration: " + dT)
            gcC = gcC.add(dT)
          case Declaration.Clashing =>
            // declarations could be incompatible; further comparison needed
            reportError("declaration clash")(d)
          case Declaration.Independent =>
            throw IError("impossible case")
        }
      }
      gcC != old
    }
    // skip empty todos, repeat until no todos are left
    while ({todo = todo.dropWhile(_.decls.isEmpty); todo.nonEmpty}) {
      // take off the first among the todos
      val current = todo.head
      val d = current.decls.head
      todo = current.tail :: todo.tail
      // check it if necessary
      val dC = if (current.alsoCheck) checkDeclaration(gcC, d) else d
      // flatten the current declaration and move the result to 'done'
      val changed = add(dC, current)
      // if it is a non-redundant include, queue the body as well
      if (changed) dC match {
        case i@Include(p,_,_) =>
          val m: Module = gc.voc.lookupModule(p).getOrElse(fail("unknown module"))
          todo ::= FlattenInput(m.decls, false, Some(i))
        case _ =>
      }
    }
    // reverse 'done' while skipping redundant declarations and collecting info for totality check
    var result: List[Declaration] = Nil
    var defines: List[String] = Nil // defined symbols
    var delegates: List[Path] = Nil // defined includes
    var realizes: List[Path] = Nil  // needed for totality
    val totalDecls = gcC.parentDecls
    totalDecls.take(totalDecls.length-numPriorDecls).foreach {_d =>
      var d = _d
      d match {
        case sd: SymbolDeclaration if sd.dfO.isDefined => defines ::= sd.name
        case id: Include if id.dfO.isDefined => delegates ::= id.dom
        case id: Include if id.realize =>
          realizes ::= id.dom
          d = id.copy(realize = false).copyFrom(id) // remove realize flags, which are redundant after checking
        case _ =>
      }
      if (!d.subsumed && (keepFull || d.subsuming || d.isInstanceOf[Include])) {
        result ::= d
      }
      // reset flags to avoid messing up the state in included modules
      d.subsumed = false
      d.subsuming = false
    }
    // totality check
    if (alsoCheck) realizes.foreach {p =>
      if (delegates.contains(p)) {
        // nothing to do
      } else {
        gc.voc.lookupModule(p).get.undefined.foreach {sd =>
          if (!defines.contains(sd.name))
            reportError("missing definition of " + p / sd.name)(cause)
        }
      }
    }
    result
  }

  /** checks a declaration against a module, which may provide an expected type for the declaration
    * cases:
    * - type: type of sd may be Present/Omitted
    * - definition: sd may be Undefined/Defined
    * - inherited: theory may have No/Other/Abstract/Concrete declaration for the name
    */
  private def checkSymbolDeclaration(gc: GlobalContext, sd: SymbolDeclaration): SymbolDeclaration = {
    implicit val cause = sd
    val sdP = gc.resolveName(ClosedRef(sd.name)).flatMap(_._2) // resolveName finds both regional and global declarations
    sdP match {
      // switch on inherited
      case Some(abs: SymbolDeclaration) =>
        if (abs.kind != sd.kind) reportError("name is inherited but has kind " + abs.kind)
        // Concrete: error
        if (abs.dfO.isDefined) reportError("name is inherited and already defined")
        // Abstract: inherit type
        val expectedTp = abs.tp
        val tpC = if (!sd.tp.known) {
          // type = Omitted: use expected type
          abs.tp
        } else {
          // type = Present: must be subtype of inherited type
          checkType(gc, sd.tp, abs.tp)
        }
        sd match {
          case sd: ExprDecl =>
            // definition = Undefined: nothing to do
            // definition = Defined: check against type
            val dfC = sd.dfO.map {df => checkExpression(gc,Lambda.allowReturn(df),tpC)}
            sd.copy(tp = tpC,dfO = dfC)
          case sd: TypeDecl =>
            val dfC = sd.dfO.map {df => checkType(gc, df, tpC)}
            sd.copy(tp = tpC,dfO = dfC)
        }
      case Some(_) =>
        // Other: error
        fail("name is inherited but not a symbol")
      case None =>
        // No: check declaration without inherited type
        sd match {
          case td: TypeDecl =>
            val tpC = checkType(gc,td.tp)
            val dfOC = td.dfO map {df => checkType(gc,df,tpC)}
            td.copy(tp = tpC,dfO = dfOC)
          case sd: ExprDecl =>
            val tpC = checkType(gc,sd.tp)
            val dfC = sd.dfO map {d => checkExpression(gc,Lambda.allowReturn(d),tpC)}
            sd.copy(tp = tpC,dfO = dfC)
        }
    }
  }

  /**private def checkRegional(gc: GlobalContext, rc: RegionalContext): RegionalContext = recoverWith(rc) {
    if (rc.theory == null && rc.owner.isEmpty) fail("underspecified region")(rc)
    val (thyC,ownC) = if (rc.theory == null) {
      val (oC,oI) = inferExpressionNorm(gc, rc.owner.get)(true)
      oI match {
        case ClassType(t) => (t, Some(oC))
        case _ => fail("owner must be instance")(rc)
      }
    } else {
      val tC = checkTheory(gc,rc.theory,true)(rc.theory)
      val oC = rc.owner map {o =>
        checkExpression(gc,o,ClassType(tC))
      }
      (tC,oC)
    }
    val ctxC = checkLocal(gc.push(thyC,ownC), rc.local, false, false)
    RegionalContext(thyC,ownC,ctxC).copyFrom(rc)
  }
  */
  private def checkTheoryPath(gc: GlobalContext, p: Path)(implicit cause: SyntaxFragment) = recoverWith(p) {
    gc.resolvePath(p) match {
      case Some((pC, m: Module)) => pC
      case _ => fail("not a module")
    }
  }

  def flattenTheory(gc: GlobalContext, thy: Theory, alsoCheck: Boolean, keepFull:Boolean)(implicit cause: SyntaxFragment): Theory = recoverWith(thy) {
    if (thy.isFlat) return thy
    // TODO simply retrieve theory if physical
    val gcI = gc.enterEmpty()
    val declsC = flattenCheckDeclarations(gcI,thy.decls,alsoCheck,keepFull)
    val thyC = Theory(declsC).copyFrom(thy)
    thyC.isFlat = true
    thyC
  }
  def checkTheory(gc: GlobalContext, thy: Theory)(implicit cause: SyntaxFragment) = flattenTheory(gc,thy,true,false)

  def checkLocal(gc: GlobalContext,lc: LocalContext,allowDefinitions: Boolean,allowMutable: Boolean): LocalContext = recoverWith(lc) {
    if (!lc.namesUnique) reportError("name clash in local context")(lc)
    var gcL = gc
    val lcC = lc.map {vd =>
      val vdC = checkVarDecl(gcL,vd,allowDefinitions,allowMutable)
      gcL = gcL.append(vdC)
      vdC
    }
    lcC.copyFrom(lc)
  }

  def checkVarDecl(gc: GlobalContext,vd: VarDecl,allowDefinitions: Boolean,allowMutable: Boolean): VarDecl = {
    implicit val cause = vd
    if (vd.mutable && !allowMutable) reportError("mutable variable not allowed here")
    if (vd.defined && !allowDefinitions) reportError("defined variable not allowed here")
    val tpC = checkType(gc,vd.tp)
    val dfC = vd.dfO map {d => checkExpression(gc,Lambda.allowReturn(d),tpC)}
    val vdC = VarDecl(vd.name,tpC.skipUnknown,dfC,vd.mutable)
    vdC.copyFrom(vd)
  }

  /** gc |- sub: ctx */
  def checkSubstitution(gc: GlobalContext, sub: Substitution, ctx: LocalContext): Substitution = {
    if (sub.length != ctx.length) reportError("wrong number of substitutes")(sub)
    var subC = Substitution.empty
    (ctx.decls.reverse zip sub.decls.reverse).foreach {case (vd,df) =>
      if (vd.dfO.isDefined) reportError("defined variable in expected context")(ctx)
      if (vd.name != df.name) reportError("wrong name in substitution: " + expected(vd.name,df.name))(sub)
      val e = df.dfO.get
      val tpE = Substituter(gc, subC, vd.tp)
      val eC = checkExpression(gc, e, tpE)
      subC = subC.append(vd.name,eC)
    }
    subC.copyFrom(sub)
  }

  /** component-wise subtype check,
    * gc |- as <: bs
    * returns substitution as -> bs
    */
  def checkSubtypes(gc: GlobalContext, as: LocalContext, bs: LocalContext)(implicit cause: SyntaxFragment): Substitution = {
    if (as.length != bs.length) reportError("wrong number of components: " + as.length + ", expected " + bs.length)
    var subI = Substitution.empty
    (as.decls.reverse zip bs.decls.reverse).foreach {case (a,b) =>
      val bS = Substituter(gc,subI, b.tp)
      checkSubtype(gc, a.tp, bS)
      subI = subI.appendRename(a.name, b)
    }
    subI
  }

  /** component-wise operation on types,
    * reuses names of the first argument, and additionally returns renaming bs -> result
    * TODO substitution into union context is not well-formed; every argument must be checked individually
    */
  def typesUnionOrIntersection(union: Boolean)
                              (gc: GlobalContext, as: LocalContext, bs: LocalContext)
                              (implicit cause: SyntaxFragment): (LocalContext,Substitution) = {
    if (as.length != bs.length) reportError("wrong number of components: " + expected(as.length.toString,bs.length.toString))
    var gcI = gc
    var subI = Substitution.empty
    var abs = LocalContext.empty
    (as.decls.reverse zip bs.decls.reverse).foreach {case (a,b) =>
      if (a.defined || b.defined) reportError("union with defined variables")
      val bS = Substituter(gcI, subI, b.tp)
      val ab = if (union) typeUnion(gcI, a.tp, bS) else typeIntersection(gcI, a.tp, bS)
      val vd = VarDecl(a.name, ab)
      abs = abs append vd
      gcI = gcI append vd
      subI = subI.appendRename(b.name, vd)
    }
    (abs,subI)
  }


  /** theory a subsumbed by b */
  def isSubtheory(a: Theory, b: Theory) = {
    a.decls.forall(b.decls.contains)
  }

  // ***************** Types **************************************
  def checkType(gc: GlobalContext,tp: Type, bound: Type): Type = {
    val tpC = checkType(gc,tp)
    checkSubtype(gc, tpC, bound)(tp)
    tpC
  }
  def checkType(gc: GlobalContext, tp: Type): Type = recoverWith(tp) {
    implicit val cause = tp
    def r(x:Type): Type = checkType(gc,x)
    disambiguateOwnedObject(gc, tp).foreach {corrected => return checkType(gc, corrected)}
    matchC(tp) {
      case r: Ref =>
        val (rC, sdO) = gc.resolveName(r).getOrElse(fail("unknown identifier"))
        val sd = sdO.getOrElse("identifier not a symbol")
        (rC,sd) match {
          case (rC: Ref, _: TypeDecl) =>
            // type ref
            rC
          case (rC: Ref, ed: ExprDecl) =>
            // expression ref, try to coerce to type
            Normalize(gc,ed.tp) match {
              case ClassType(d) => gc.push(d).lookupRegional(MagicFunctions.asType) match {
                case Some(_: TypeDecl) =>
                  PurityChecker(gc,rC.asInstanceOf[Expression])
                  MagicFunctions.typeOf(rC,d)
                case _ => fail("no type coercion in type")
              }
              case _ => fail("expression cannot be coerced to a type")
            }
          case (rC:OpenRef, m: Module) =>
            // module ref, interpret as class type
            if (!m.closed) reportError("open module not a type")
            ClassType(PhysicalTheory(rC.path))
          case _ => fail("not a type")
        }
      case OwnedType(owner,dom,tp) =>
        val (ownerC,ownerI) = inferExpressionNorm(gc,owner)(true)
        PurityChecker(ownerC)(gc,())
        ownerI match {
          case ClassType(domC) =>
            if (dom != null && dom != domC) reportError("unexpected theory")
            val envO = gc.push(domC,Some(ownerC))
            val tpC = checkType(envO,tp)
            OwnedType(ownerC,domC,tpC)
          case _ => fail("owner must be an instance")
        }
      case _: BaseType | ExceptionType => tp
      case IntervalType(l,u) =>
        val lC = l map {e => checkExpressionPure(gc,e,IntType)}
        val uC = u map {e => checkExpressionPure(gc,e,IntType)}
        IntervalType(lC,uC)
      case CollectionType(a,k) => CollectionType(r(a),k)
      case ProdType(as) => ProdType(checkLocal(gc,as,false,false))
      case FunType(as,b) =>
        val asC = checkLocal(gc,as,false,false)
        val bC = checkType(gc.append(asC),b)
        FunType(asC,bC)
      case ClassType(thy) =>
        val thyC = checkTheory(gc,thy)(tp)
        ClassType(thyC)
      case ExprsOver(sc,q) =>
        val scC = checkTheory(gc,sc)(tp)
        val qC = checkType(gc.push(scC),q)
        ExprsOver(scC,qC)
      case ProofType(f) =>
        val fC = checkExpressionPure(gc,f,BoolType)
        ProofType(fC)
      case u: UnknownType =>
        if (u.known) {
          checkType(gc,u.skipUnknown)
        } else {
          if (u.originalContext != null || u.sub != null) {
            throw IError("unexpected context in unknown type") // never happens anyway
          } else {
            UnknownType(gc,u.container,gc.visibleLocals.identity) // set up for later inference
          }
        }
    }
  }

  /** a <: b */
  def checkSubtype(gc: GlobalContext, a: Type, b: Type)(implicit cause: SyntaxFragment): Unit = {
    val equated = equateTypes(gc,a,b)(Some(true))
    if (equated) return
    (a,b) match {
      case (_,AnyType) => AnyType
      case (EmptyType,_) =>
      case (_:IntervalType,(IntType|RatType)) =>
      case (IntType,RatType) =>
      case (a: IntervalType, b: IntervalType) =>
        (a.lower,b.lower) match {
          case (_,None) =>
          case (None,Some(_)) => reportError("interval is not subtype")
          case (Some(i),Some(j)) =>
            val c = simplifyExpression(gc,GreaterEq(i,j))
            if (c == BoolValue(true)) {}
            else if (c == BoolValue(false)) reportError("interval is not subtype")
            else {reportError("interval type not checked")} // type-checking incomplete}
        }
        (a.upper,b.upper) match {
          case (_, None) =>
          case (None, Some(_)) => reportError("interval is not subtype")
          case (Some(i), Some(j)) =>
            val c = simplifyExpression(gc, LessEq(i,j))
            if (c == BoolValue(true)) {}
            else if (c == BoolValue(false)) reportError("interval is not subtype")
            else {reportError("interval type not checked")}// type-checking incomplete}
        }
      case (CollectionType(a,k),CollectionType(b,l)) =>
        if (!(k sub l)) reportError(s"collection type $k is not subtype of collection type $l")
        checkSubtype(gc,a,b)
      case (ProdType(as),ProdType(bs)) =>
        checkSubtypes(gc, as, bs)
      case (FunType(as,o),FunType(bs,p)) =>
        checkSubtypes(gc, bs, as)
        checkSubtype(gc.append(bs),o,p)
      case (ExprsOver(aT,u),ExprsOver(bT,v)) =>
        if (!isSubtheory(aT,bT)) reportError("not quoted from the same theory")
        checkSubtype(gc.push(aT),u,v)
      case (ClassType(aT),ClassType(bT)) =>
        // model of aT or model of bT, i.e., model of intersection
        if (!isSubtheory(bT,aT)) // larger theory = smaller type
          reportError("subtype must be larger theory")
      case _ =>
        val aN = Normalize(gc,a)
        val bN = Normalize(gc,b)
        if (a != aN || b != bN)
          checkSubtype(gc,aN,bN)
        else
          reportError(s"found: $a; expected: $b")
    }
  }

  /** flattened if the inputs are */
  def typeUnion(gc: GlobalContext,tps: List[Type])(implicit cause: SyntaxFragment): Type = {
    if (tps.isEmpty) {
      EmptyType
    } else {
      var res: Type = tps.head
      tps.tail.foreach {tp => res = typeUnion(gc,res,tp)}
      res
    }
  }

  /** least common supertype
    * flattened if the inputs are
    */
    //TODO type bounds
  def typeUnion(gc: GlobalContext,a: Type,b: Type)(implicit cause: SyntaxFragment): Type = {
    // equality, possibly by inference
    val equated = equateTypes(gc,a,b)(Some(true))
    if (equated) return b
    // proper subtyping
    (a,b) match {
      case (AnyType,_) | (_,AnyType) => AnyType
      case (EmptyType,t) => t
      case (t,EmptyType) => t
      case (IntType,RatType) | (RatType,IntType) => RatType
      case (_: IntervalType, t@(IntType|RatType)) => t
      case (t@(IntType|RatType), _: IntervalType) => t
      case (a: IntervalType, b: IntervalType) =>
        val l = (a.lower,b.lower) match {
          case (Some(i),Some(j)) => Some(Minimum(i,j))
          case _ => None
        }
        val u = (a.upper,b.upper) match {
          case (Some(i),Some(j)) => Some(Maximum(i,j))
          case _ => None
        }
        IntervalType(l,u)
      case (CollectionType(a,k),CollectionType(b,l)) => CollectionType(typeUnion(gc,a,b), k union l)
      case (ProdType(as),ProdType(bs)) =>
        val (abs,_) = typesUnionOrIntersection(true)(gc,as,bs)
        ProdType(abs)
      case (FunType(as,o),FunType(bs,p)) =>
        val (abs,sub) = typesUnionOrIntersection(false)(gc, as, bs)
        val gcI = gc.append(abs)
        val pS = Substituter(gcI, sub, p)
        val op = typeUnion(gcI,o,pS)
        FunType(abs,op)
      case (ExprsOver(aT,u), ExprsOver(bT, v)) =>
        if (aT != bT) reportError("not quoted from the same theory")
        val thyU = theoryUnion(gc, aT, bT)
        // aT-expression of type u or bT-expression of type v, i.e., expression over union of union type
        ExprsOver(thyU, typeUnion(gc.push(thyU), u, v))
      case (ClassType(aT), ClassType(bT)) =>
        // model of aT or model of bT, i.e., model of intersection
        val i = theoryIntersection(gc,aT,bT)
        if (i.decls.isEmpty) AnyType else ClassType(i)
      case _ =>
        val aN = Normalize(gc,a)
        val bN = Normalize(gc,b)
        if (aN != a || bN != b)
          typeUnion(gc, aN, bN)
        else
          AnyType
    }
  }

  /** greatest common subtype
    * flattened if the inputs are
    */
   //TODO type bounds
  def typeIntersection(gc: GlobalContext, a: Type, b: Type)(implicit cause: SyntaxFragment): Type = {
     val equated = equateTypes(gc,a,b)(Some(true))
     if (equated) return a
    (a,b) match {
      case (AnyType,t) => t
      case (t,AnyType) => t
      case (EmptyType,_) | (_,EmptyType) => EmptyType
      case (IntType,RatType) | (RatType,IntType) => IntType
      case (t: IntervalType, (IntType|RatType)) => t
      case ((IntType|RatType), t: IntervalType) => t
      case (a: IntervalType, b: IntervalType) =>
        val l = (a.lower,b.lower) match {
          case (Some(i),Some(j)) => Some(Maximum(i,j))
          case (a,None) => a
          case (None,b) => b
        }
        val u = (a.upper,b.upper) match {
          case (Some(i),Some(j)) => Some(Minimum(i,j))
          case (a,None) => a
          case (None,b) => b
        }
        IntervalType(l,u)
      case (CollectionType(a,k),CollectionType(b,l)) => CollectionType(typeIntersection(gc,a,b), k inter l)
      case (ProdType(as),ProdType(bs)) if as.length == bs.length =>
        val (abs,_) = typesUnionOrIntersection(false)(gc,as,bs)
        ProdType(abs)
      case (FunType(as,o),FunType(bs,p)) if as.length == bs.length =>
        val (abs,sub) = typesUnionOrIntersection(true)(gc,as,bs)
        val gcI = gc.append(abs)
        val pS = Substituter(gcI,sub,p)
        val op = typeIntersection(gcI,o,pS)
        FunType(abs,op)
      case (ExprsOver(aT,u), ExprsOver(bT, v)) =>
        // aT-expression of type u and bT-expression of type v, i.e., expression over the intersection of intersection type
        val thyI = theoryIntersection(gc, aT, bT)
        val thyU = theoryUnion(gc, aT, bT)
        ExprsOver(thyI, typeIntersection(gc.push(thyU), u, v))
      case (ClassType(aT), ClassType(bT)) =>
        // model of aT and of bT, i.e., model of the union
        ClassType(theoryUnion(gc,aT,bT))
      case _ =>
        val aN = Normalize(gc,a)
        val bN = Normalize(gc,b)
        if (aN != a || bN != b)
          typeIntersection(gc, aN, bN)
        else
          EmptyType
    }
  }

  /** union (colimit) of theories */
  def theoryUnion(gc: GlobalContext, a: Theory, b: Theory): Theory = {
    val pqs = (a.decls ::: b.decls).distinct //TODO error if not compatible
    val thy = Theory(pqs)
    thy.isFlat = a.isFlat && b.isFlat // flat if the inputs are
    thy
  }

  /** intersection of theories: the union of all common includes */
  def theoryIntersection(gc: GlobalContext, a: Theory, b: Theory): Theory = {
    val pqs = a.decls intersect b.decls // TODO remove definiens if not the same
    val thy = Theory(pqs)
    thy.isFlat = a.isFlat && b.isFlat // flat if the inputs are
    thy
  }

  /** normalizes a type: definitions expanded, but not flattened */
  // TODO: cache being normal
  object Normalize extends StatelessTraverser {
    override def apply(thy: Theory)(implicit gc: GlobalContext, a:Unit) = {
      // possible infinite loop if keepFull==true
      val thyF = flattenTheory(gc,thy,false,false)(thy)
      super.apply(thyF)
    }
    override def apply(exp: Expression)(implicit gc: GlobalContext, a:Unit) = {
      exp
    }
    override def apply(tp: Type)(implicit gc: GlobalContext, a:Unit): Type = {
      matchC(tp) {
        case r: Ref => gc.lookupRef(r) match {
          case Some(td: TypeDecl) => td.dfO match {
            case Some(df) => apply(df)
            case None => r
          }
          case _ => fail("illegal type")(tp) // impossible if tp is checked
        }
        case OwnedType(own,_,t) =>
          // we must reinfer the domain because the fields in the cached domain may have acquired definitions
          // when the object was moved into another region
          val ownI = inferCheckedExpression(gc,own) match {
            case ct:ClassType => ct
            case t => apply(t)
          }
          val dom = ownI match {
            case ClassType(d) => d
            case _ => throw IError("unexpected type")
          }
          val tN = apply(gc.push(dom,Some(own)), t)
          val tpN = OwnerSubstitutor(own,dom,tN)
          if (tpN != tp) apply(tpN) else tpN
        case IntervalType(l,u) =>
          applyDefault(tp) match {
            case (IntervalType(Some(IntValue(l)),Some(IntValue(u)))) if l > u => EmptyType
            case IntervalType(None,None) => IntType
            case tpN => tpN
          }
        case _ => applyDefault(tp)
      }
    }
  }

  // ***************** Expressions **************************************
  /** checks an expression against an expected type
    *
    * This is helpful for infering omitted information in introduction forms from their expected type.
    * In most cases, this defers to type inference and subtype checking.
    */
  def checkExpression(gc: GlobalContext,exp: Expression,tp: Type): Expression = recoverWith(exp) {
    implicit val cause = exp
    disambiguateOwnedObject(gc, exp).foreach {corrected => return checkExpression(gc, corrected, tp)}
    val tpN = Normalize(gc,tp)
    val eC: Expression = (exp,tpN) match {
      case (i, IntervalType(l,u)) =>
        val (iC,iI) = inferExpressionNorm(gc,i)(true)
        iI match {
          case IntType =>
            // inference of values return Int, so we need to see if we can downcast
            val lCond = l map {b => LessEq(b,iC)} getOrElse BoolValue(true)
            val uCond = u map {b => LessEq(iC,b)} getOrElse BoolValue(true)
            simplifyExpression(gc, And(lCond,uCond)) match {
              case BoolValue(true) =>
              case BoolValue(false) => reportError("out of interval")
              case _ => reportError("cannot determine interval mebmership")// incomplete
            }
          case _ =>
            checkSubtype(gc,iI,tpN)
        }
        iC
      case (CollectionValue(es), CollectionType(t,kind)) =>
        if (kind.sizeOne && es.length > 1) reportError("option type must have at most one element")
        val esC = es.map(e => checkExpression(gc,e,t))
        CollectionValue(esC)
      case (Tuple(es),ProdType(ts)) =>
        if (es.length != ts.length) reportError("wrong number of components in tuple")
        val esC = checkSubstitution(gc, ts.substitute(es), ts)
        Tuple(esC.exprs)
      case (Lambda(ins,bd,mr), ft) =>
        // this handles arbitrary function types so that we can always insert the return variable if necessary
        val insC = checkLocal(gc,ins,false,false)
        val gcI = gc.append(insC)
        val outType = ft match {
          case FunType(insE,outE) =>
            val ren = checkSubtypes(gc, insE, insC)
            Substituter(gcI, ren, outE)
          case _ =>
            val o = Type.unknown(gcI)
            checkSubtype(gc, FunType(insC,o), ft)
            o
        }
        val gcB = if (mr) gcI.append(VarDecl.output(outType)) else gcI
        val bdC = checkExpression(gcB,bd,outType)
        Lambda(insC,bdC,mr)
      case (OwnedExpr(oe, de, e), OwnedType(ot, dt, tp)) if oe == ot =>
        val (oC,oI) = inferExpression(gc, oe)(true)
        oI match {
          case ClassType(dC) =>
            if ((de != null && de != dC) || (dt != null && dt != dC)) reportError("unexpected given theory")
            val eC = checkExpression(gc.push(dC,Some(oC)), e, tp)
            OwnedExpr(oC, dC, eC)
          case _ => fail("owner must be class type")
        }
      case (Instance(thyA), ClassType(thyB)) =>
        val instC = checkTheory(gc, thyB union thyA)
        Instance(thyA)
      case (ExprOver(scE,e), ExprsOver(scT, tp)) =>
        val scTC = checkTheory(gc, scT)
        if (scE != null) {
          if (!isSubtheory(scE, scTC)) reportError("quoted scope not part of expected type")
        }
        val eC = checkExpression(gc.push(scTC), e, tp)
        ExprOver(scTC, eC)
      case (Eval(q), a) =>
        val qC = checkExpression(gc.pop(), q, ExprsOver(gc.theory, a))
        Eval(qC)
      case (Application(op: BaseOperator,args),_) if !op.tp.known =>
        val (argsC,argsI) = args.map(a => inferExpression(gc,a)(true)).unzip
        val opTp = FunType.simple(argsI,tpN)
        val opC = checkExpression(gc,op,opTp)
        Application(opC,argsC)
      case (BaseOperator(op,opTp),ft:FunType) =>
        opTp.skipUnknown match {
          case u: UnknownType =>
            if (!ft.simple) reportError("operators cannot have dependent type")
            if (u.originalContext != null || u.sub != null) throw IError("unexpected context in unknown operator type")
            val outI = inferOperator(gc,op,ft.simpleInputs)
            checkSubtype(gc,outI,ft.out)
            u.set(ft) // just in case this unknown was referenced elsewhere
          case _ =>
            checkSubtype(gc,opTp,ft)
        }
        BaseOperator(op,ft)
      case (Block(es), _) =>
        var gcL = gc // local environment, includes variables seen in the block so far
        val numExprs = es.length
        if (numExprs == 0) {
          // empty block has unit type
          checkSubtype(gc,UnitType,tpN)
        }
        var i = 0
        val esC = es.map {e =>
          i += 1
          if (i == numExprs) {
            // the last expression in the block determines the type
            checkExpression(gcL, e, tpN)
          } else {
            // other expressions can have any type
            val (eC,_) = inferExpression(gcL,e)(true)
            // remember variables for later expressions
            val eDs = LocalContext.collectContext(eC)
            if (!eDs.namesUnique)
              reportError("clashing names declared in expression")
            gcL = gcL.append(eDs)
            eC
          }
        }
        Block(esC)
      // TODO there are more opportunities to pass on the expected type: If, Match, ListElem, Proj, ... (but only if the expected is known)
      case _ =>
        val (eC,eI) = inferExpression(gc,exp)(true)
        val mf = new MagicFunctions(gc)
        (tp,eI) match {
          case (StringType, mf.asstring(dom,StringType)) =>
            mf.asstring.insert(dom,eC,Nil)
          case (s:CollectionType, mf.iteration(dom,t:CollectionType)) =>
            checkSubtype(gc,t,s)
            mf.iteration.insert(dom,eC,Nil)
          case _ =>
            checkSubtype(gc,eI,tpN)
            eC
        }
    }
    eC.copyFrom(exp)
    eC
  }

  /** infers by checking against an unknown type, useful to share code between the cases for inferExpression and checkExpression */
  private def inferExpressionViaCheck(gc: GlobalContext, exp: Expression): (Expression,Type) = {
    val u = Type.unknown(gc)
    val eC = checkExpression(gc,exp, u)
    (eC, u.skipUnknown)
  }

  /** infers the type of an expression that has already been checked (skips all checks) */
  def inferCheckedExpression(gc: GlobalContext, exp: Expression) = inferExpression(gc, exp)(false)._2
  def checkAndInferExpression(gc: GlobalContext, exp: Expression) = inferExpression(gc, exp)(true)

  def checkExpressionPure(gc: GlobalContext, e: Expression, t: Type) = {
    val eC = checkExpression(gc, e, t)
    PurityChecker(gc,eC)
    eC
  }

  /** like check, but also infers a context with the free variables */
  def checkExpressionPattern(gc: GlobalContext, e: Expression, tp: Type) = {
    // TODO: this interprets any name bound in the context as a constant pattern, rather than shadowing it
    val fvs = FreeVariables.infer(gc,e)
    var fctxI = LocalContext.empty
    var gcI = gc
    fvs.foreach {n =>
      val vd = VarDecl(n, Type.unknown(gcI))
      fctxI = fctxI append vd
      gcI = gcI append vd
    }
    val eC = checkExpression(gcI, e, tp)
    val fctxIS = fctxI.map {vd =>
      if (!vd.tp.known) reportError("free variable whose type cannot be infered: " + vd.name)(e)
      vd.copy(tp = vd.tp.skipUnknown)
    }
    PatternChecker(gc,eC)
    (fctxIS, eC)
  }

  /** like [[inferExpression]] but with the type normalized */
  def inferExpressionNorm(gc: GlobalContext,e: Expression)(implicit alsoCheck: Boolean): (Expression,Type) = {
    val (eC,eI) = inferExpression(gc, e)
    (eC, Normalize(gc,eI))
  }

  /** checks an expression and infers its type
    *
    * This defers to [[checkExpression]] if it knows the expected type.
    */
  def inferExpression(gc: GlobalContext,expA: Expression)
                     (implicit alsoCheck: Boolean): (Expression,Type) = recoverWith[(Expression,Type)]((expA,AnyType)) {
    implicit val cause = expA
    val mf = new MagicFunctions(gc)
    // exp != expA only if exp is an unresolved reference
    val (expR, sdCached) = gc.resolveName(expA).getOrElse(fail("unknown identifier " + expA))
    val exp = expR match {
      case e: Expression => e
      case _ => fail("not an expression")
    }
    if (alsoCheck)
      disambiguateOwnedObject(gc, exp).foreach {corrected => return inferExpression(gc, corrected)}
    // check exp and infer its type
    val (expC,expI): (Expression,Type) = exp match {
      case e: BaseValue => (e,e.tp)
      case op: BaseOperator =>
        if (!op.tp.known) {
          reportError("cannot infer type of operator")
        }
        val ft = Normalize(gc,op.tp) match {
          case ft: FunType if ft.simple => ft
          case _ => fail("operator type not a simple function")
        }
        val out = inferOperator(gc,op.operator,ft.simpleInputs)
        if (alsoCheck)
          checkSubtype(gc,out,ft.out)(exp)
        (BaseOperator(op.operator,ft),op.tp)
      case r: OpenRef =>
        val (rC,rd) = sdCached match {
          case Some(d) => (r, d)
          case _ => checkOpenRef(gc,r)
        }
        rd match {
          case ed: ExprDecl => (rC,ed.tp)
          case _ => fail(s"$rC is not an expression")
        }
      case ClosedRef(n) =>
        sdCached match {
          case Some(ed: ExprDecl) => (exp, ed.tp)
          case _ => fail("not an expression")
        }
      case This(l) =>
        if (l<=0) fail("illegal level")
        if (gc.regions.length < l) fail("level does not exist")
        val (skipped,rest) = gc.regions.splitAt(l-1)
        val reg = rest.head
        if (skipped.exists(!_.transparent))
          fail("level is not accessible")
        reg.physical match {
          case Some(false) => fail("parent is not a theory")
          case _ => (exp,ClassType(reg.region.theory))
        }
      case OwnedExpr(owner, dom, e) =>
        val (ownerC, ownerI) = if (alsoCheck) inferExpressionNorm(gc, owner) else (owner, ClassType(dom))
        ownerI match {
          case ClassType(domC) =>
            if (alsoCheck)
              if (dom != null && dom != domC) fail("unexpected given theory")
            val envO = gc.push(domC,Some(ownerC))
            val (eC, eI) = inferExpression(envO, e)
            (OwnedExpr(ownerC, domC, eC), OwnedType(ownerC, domC, eI))
          case _ => fail("owner must be an instance")
        }
      case VarRef(n) =>
        val vd = gc.lookupLocal(n).getOrElse {fail("undeclared variables")}
        (exp,vd.tp)
      case Instance(thy) =>
        val thyC = if (!alsoCheck) thy else {
          val thyR = thy match {
            case ExtendedTheory(p,ds) => Theory(Include(p,None,true) :: ds)
            case _ => fail("instance must be of atomic theory")
          }
          // TODO: check that ds do not have side effects outside of itself
          if (alsoCheck) checkTheory(gc,thyR) else thyR
        }
        (Instance(thyC),ClassType(thyC))
      case ExprOver(sc,q) =>
        val scC = if (alsoCheck) checkTheory(gc,sc) else sc
        val (qC,qI) = inferExpression(gc.push(scC),q)
        (ExprOver(scC,qC),ExprsOver(scC,qI))
      case Eval(e) =>
        if (alsoCheck)
          if (gc.regions.isEmpty) fail("eval outside quotation")
        val (eC,eI) = inferExpressionNorm(gc.pop(),e)
        eI match {
          case ExprsOver(eT,q) =>
            if (alsoCheck)
              if (!isSubtheory(eT, gc.theory)) fail("quoted over wrong theory")
            (Eval(eC),q)
          case mf.evaluation(dom,a) =>
            (mf.evaluation.insert(dom,eC, Nil), a)
          case _ => fail("not a quoted expression")
        }
      case MatchCase(ctx, p, b) =>
        fail("match case outside of match")
      case Lambda(ins,bd,mr) =>
        val insC = if (alsoCheck) checkLocal(gc,ins,false,false) else ins
        val (bdC,bdI) = inferExpression(gc.append(insC),bd)
        (Lambda(insC,bdC,mr),FunType(insC,bdI))
      case Application(f,as) =>
        f match {
          case op: BaseOperator if !op.tp.known =>
            // for an operator of unknown type, we need to infer the argument types first
            val (asC,asI) = as.map(a => inferExpression(gc,a)).unzip
            val out = inferOperator(gc,op.operator,asI)
            val opC = op.copy(tp = FunType.simple(asI,out))
            (Application(opC,asC),out)
          case f =>
            val (fC,fI) = inferExpressionNorm(gc,f)
            val (fM,ins,out) = fI match {
              case FunType(i,o) => (fC,i,o)
              case ProdType(ys) =>
                as match {
                  case List(IntValue(i)) =>
                    // projections are parsed as applications
                    return inferExpression(gc, Projection(f,i.toInt).copyFrom(exp))
                  case _ => fail("not a function")
                }
              case ExprsOver(thy, _) =>
                // coerce quoted function into function
                val eC = ExprOver(thy, Application(Eval.reduced(fC), as map Eval.reduced))
                return inferExpression(gc, eC)
              case u: UnknownType if !u.known && u.sub.isIdentity =>
                var uis = LocalContext.empty
                var gcI = u.originalContext
                val n = gcI.freshName
                Range(0,as.length).foreach {i =>
                  val vd = VarDecl(n + "_" + i.toString, Type.unknown(gcI))
                  uis = uis append vd
                  gcI = gc append vd
                }
                val uo = Type.unknown(gcI)
                u.set(FunType(uis,uo))
                (fC,uis,uo)
              case mf.application(dom,FunType(i,o)) => (mf.application.insert(dom,fC,as),i,o)
              case _ => fail("not a function")(f)
            }
            if (ins.length != as.length) fail("wrong number of arguments")
            val sub = ins.substitute(as)
            val asC = if (alsoCheck) {
              checkSubstitution(gc,sub,ins)
            } else sub
            val outS = Substituter(gc,asC,out)
            (Application(fM,asC.exprs),outS)
        }
      case Tuple(es) =>
        val (esC,esI) = es.map(e => inferExpression(gc,e)).unzip
        (Tuple(esC),ProdType.simple(esI))
      case Projection(tup, p) =>
        val mfp = new mf.projection(p)
        val (tupC,tupI) = inferExpressionNorm(gc,tup)
        tupI match {
          case ProdType(ts) =>
            if (alsoCheck) {
              if (p <= 0) fail("non-positive index")
              if (p > ts.length) fail("index out of bounds")
            }
            val componentType = ts(p-1).tp // -1 because components start at 1 but declarations at 0
            val precedingCompDecls = ts.take(p-1)
            val precedingProjs = Range(1,p).toList.map(i => Projection(tup, i))
            val sub = precedingCompDecls.substitute(precedingProjs)
            val projI = Substituter(gc,sub,componentType)
            (Projection(tupC,p), projI)
          case mfp(dom,a) =>
            (mfp.insert(dom,tupC, List(IntValue(p))), a)
          case _ => fail("not a tuple")
        }
      case CollectionValue(es) =>
        val (esC,esI) = es.map(e => inferExpression(gc,e)).unzip
        val eI = typeUnion(gc,esI)
        val kind = if (es.length <= 1) CollectionKind.Option else CollectionKind.List // smallest applicable subquotient of List
        (CollectionValue(esC),CollectionType(eI, kind))
      case ListElem(l, p) =>
        if (alsoCheck) {
          val u = Type.unknown(gc)
          val lC = checkExpression(gc,l,CollectionType(u,CollectionKind.UList))
          val pC = checkExpression(gc,p,IntType)
          // index bounds not checked
          (ListElem(lC,pC),u)
        } else {
          val (_,CollectionType(a,_)) = inferExpression(gc,l)
          (exp,a)
        }
      case Quantifier(q,vars,bd) =>
        val eC = if (alsoCheck) {
          val varsC = checkLocal(gc,vars,false,false)
          val bdC = checkExpressionPure(gc.append(varsC),bd,BoolType)
          Quantifier(q,varsC,bdC)
        } else exp
        (eC, BoolType)
      case Assert(f) =>
        val fC = if (alsoCheck) checkExpressionPure(gc, f, BoolType) else f
        (Assert(fC), UnitType)
      case Block(es) =>
        if (alsoCheck) {
          inferExpressionViaCheck(gc, exp)
        } else {
          // infer last element in context of previous ones
          val tp = if (es.isEmpty) UnitType else {
            var gcL = gc
            es.init.foreach {e => gcL = gcL.append(LocalContext.collectContext(e))}
            inferCheckedExpression(gcL, es.last)
          }
          (exp,tp)
        }
      case VarDecl(n, tp, dfO, mut, output) =>
        if (alsoCheck) {
          val tpC = checkType(gc,tp)
          val dfOC = dfO map {df => checkExpression(gc,df,tpC)}
          (VarDecl(n,tpC,dfOC,mut,output),tpC) // evaluates to VarRef(n); that allows introducing names in the middle of expressions
        } else (exp,tp)
      case Assign(e,df) =>
        val expC = if (alsoCheck) {
          val (eC,eI) = inferExpression(gc,e)
          val dfC = checkExpression(gc,df,eI)
          checkAssignable(gc,e)
          Assign(eC,dfC)
        } else exp
        (expC,UnitType)
      case While(cond,bd) =>
        val expC = if (alsoCheck) {
          val condC = checkExpression(gc,cond,BoolType)
          val bdC = checkExpression(gc,bd,AnyType)
          While(condC,bdC)
        } else exp
        (expC,UnitType)
      case IfThenElse(cond,thn, elsO) =>
        val condC = if (alsoCheck) checkExpression(gc, cond, BoolType) else cond
        val (thnC,thnI) = inferExpressionNorm(gc, thn)
        val (elsOC, eI) = elsO match {
          case Some(els) =>
            val (elsC, elsI) = inferExpressionNorm(gc, els)
            val u = typeUnion(gc, thnI, elsI)
            if (u == AnyType) reportError(s"branches have incompatible types: $thnI vs. $elsI")
            (Some(elsC), u)
          case None => (None,UnitType)
        }
        (IfThenElse(condC, thnC, elsOC), eI)
      case Match(e,cs,h) =>
        val (eC,eI) = inferExpressionNorm(gc,e)
        if (!alsoCheck) {
          val tp = if (h) eI else {
            val csI = cs.map {case MatchCase(ctx,_,b) => inferCheckedExpression(gc.append(ctx),b)}
            typeUnion(gc, csI)
          }
          (exp,tp)
        } else {
          val (patType,bodyType) = if (h) {
            (ExceptionType,Some(eI))
          } else {
            (eI,None)
          }
          val (csC,csI) = cs.map {case MatchCase(ctx,p,b) =>
            val (ctxC,pC) = if (ctx == null) {
              checkExpressionPattern(gc,p,patType)
            } else {
              val cC = checkLocal(gc,ctx,false,false)
              (cC,checkExpression(gc.append(cC),p,patType))
            }
            val (bC,bI) = bodyType match {
              case None => inferExpression(gc.append(ctxC),b)
              case Some(bt) => (checkExpression(gc.append(ctxC),b,bt),bt)
            }
            (MatchCase(ctxC,pC,bC),bI)
          }.unzip
          val mI = if (h) eI else typeUnion(gc,csI)
          if (mI == AnyType) reportError(s"branches have incompatible types: " + csI.mkString(", "))
          (Match(eC,csC,h),mI)
        }
      case For(vd, range, bd) =>
        val vdC = checkVarDecl(gc,vd,false,false)
        val rangeC = checkExpression(gc, range, CollectionKind.UList(vdC.tp))
        val (bdC,bdI) = inferExpression(gc.append(vdC), bd)
        (For(vdC, rangeC, bdC), CollectionKind.List(bdI)) // map may introduce repetitions
      case Return(e,thrw) =>
        val eC = if (alsoCheck) {
          val rt = if (thrw) ExceptionType else gc.getOutput.getOrElse(fail("return not allowed here"))
          checkExpression(gc,e,rt)
        } else e
        (Return(eC,thrw), EmptyType)
    }
    val expCF = if (alsoCheck) expC.copyFrom(exp) else expC
    (expCF,expI)
  }

  /** checks if an expression may be used as a pattern */
  private object PatternChecker extends StatelessTraverser {
    override def apply(e: Expression)(implicit gc: GlobalContext,a:Unit): Expression = e match {
      case _: Tuple | _: CollectionValue | Application(_:OpenRef,_) => applyDefault(e)
      case _: BaseValue | _: VarRef => e
      case vd: VarDecl if vd.dfO.isEmpty => e
      case r: OpenRef => gc.lookupRef(r) match {
        case Some(ed: ExprDecl) if !ed.mutable && ed.dfO.isEmpty => e
        case _ => fail("defined function in pattern")(e)
      }
      case _: ExprOver => e
      case Application(bo: BaseOperator, args) =>
        if (bo.operator.invertible) {args map apply; e} else fail("non-invertible operator in pattern")(e)
      case _ => fail("non-constructor in pattern")(e)
    }
  }

  /**
    * An expression may be impure in multiple ways:
    * - partial: return no value (while, return/throw)
    * - non-deterministic: return different values in different executions (reading from a mutable identifier, IO reads, instance creation)
    * - effectful: change the environment (assign to a mutable identifier, any IO)
    * All are undecidable so that we can only check sufficient criteria for purity.
    *
    * The following are always pure:
    * - references to immutable identifiers (even if their initializers are absent or impure)
    * - lambdas (even if their bodies are impure)
    * - quotations with pure evals (even if the quoted expression is impure)
    *
    * A function application is pure if the resulting beta-reduction is guaranteed to be.
    * TODO "pure" keyword needed to allow abstract identifiers in pure position.
    *
    * The following expressions must be pure
    * - initializers of regional identifiers (including fields of theories, instances)
    * - subexpressions of types (including those that are subexpressions of pure expressions)
    * - quantified formulas
    * - patterns in matches or assignments
    * The following expressions must not have side-effects
    * - Boolean conditions in if, while, assert
    * - Evals and operator arguments (to avoid specifying their order of evaluation)
    * - elements in a tuple or a collection value???
    */
  private object PurityChecker extends StatelessTraverser {
    override def apply(e: Expression)(implicit gc: GlobalContext,a:Unit) = {
      def isNot(m: String) = fail("must be " + m)(e)
      e match {
        case r:Ref => gc.lookupRef(r) match {
          case Some(ed: ExprDecl) => if (ed.mutable) isNot("deterministic")
          case _ =>
        }
        case VarRef(n) => if (gc.lookup(n).mutable) isNot("determinisitic")
        case _: Instance => isNot("deterministic")
        case _: Assign => isNot("effect-free")
        // match ???
        case _: While => isNot("total")
        case _: Return => isNot("total")
        case _: Lambda =>
        case _ => applyDefault(e)
      }
      e
    }
  }

  private def checkAssignable(gc: GlobalContext, target: Expression): Unit = {
    def check(t: Expression) = checkAssignable(gc, t)
    implicit val cause = target
    target match {
      case VarRef("") => // anonyomous variable
      case VarRef(n) =>
        val vd = gc.local.lookup(n)
        if (!vd.mutable) fail("variable not mutable")
      case vd: VarDecl =>
        if (vd.defined) fail("defined variable not assignable")
      case ClosedRef(n) => gc.lookupRegional(n) match {
        case Some(ed: ExprDecl) =>
          if (!ed.mutable) fail("assignment to immutable field")
        case _ => fail("not an assignable field")
      }
      case Tuple(es) => es foreach check
      case CollectionValue(es) => es foreach check // TODO depends on kind
      case eo: ExprOver => EvalTraverser(eo) {e => check(e); e}
      case Application(OpenRef(r),es) =>
        gc.lookupGlobal(r) match {
          case Some(ed: ExprDecl) if ed.dfO.isEmpty =>
          case _ => fail("function application not assignable")
        }
        es foreach check
      case Application(BaseOperator(o,_),es) =>
        if (!o.invertible) fail("operator not invertible")
        es foreach check
      case _ => fail("expression not assignable")
    }
  }

  // TODO requires purity checks
  def simplifyExpression(gc: GlobalContext, exp: Expression) = Simplify(gc,exp)

  // ************ auxiliary functions for handling identifiers (sharing code for types and expressions)

  /** disambiguate single-segment identifiers that the parser may have left ambiguous
    * resolving can involve retrieving the declaration, which can be expensive; so we return it if we find one
    */
  private def checkOpenRef(gc: GlobalContext, r: OpenRef)(implicit cause: SyntaxFragment) = {
    val (pC, pd) = gc.resolvePath(r.path).getOrElse {fail("unknown identifier: " + r)}
    // TODO check that base of open module is included into current scope
    val rC = OpenRef(pC)
    (rC,pd)
  }

  /** for replacing OwnedObj with
    * - Expr[s]Over
    * - OpenRef
    * - projection
    * because the parser cannot disambiguate these
    */
  // the type bound allows taking a Type or an Expression and returning the same
  private def disambiguateOwnedObject[A >: Type with Expression](gc: GlobalContext, o: A): Option[A] = o match {
    case o: OwnedObject =>
      // if owner is module m: the path to m, and m.closed
      val ownerIsModule = o.owner match {
        case OpenRef(p) => gc.resolvePath(p) flatMap {
          case (pR, m: Module) => Some((pR, m.closed))
          case _ => None
        }
        case ClosedRef(n) => gc.resolveName(o.owner) flatMap {
          case (_:ClosedRef, Some(m:Module)) => Some((Path(n), m.closed))
          case (OpenRef(pR), Some(m:Module)) => Some((pR,m.closed))
          case _ => None
        }
        case _ => None
      }
      ownerIsModule map {case (p,closed) =>
        if (closed) {
          // rewrite to quotation
          val sc = PhysicalTheory(p)
          o match {
            case o: OwnedType => ExprsOver(sc,o.owned).copyFrom(o).asInstanceOf[A] // guaranteed to work, but needed by Scala compiler
            case o: OwnedExpr => ExprOver(sc,o.owned).copyFrom(o).asInstanceOf[A]
          }
        } else {
          // only legal if M.n is meant to be an OpenRef
          o.owned match {
            case ClosedRef(n) => OpenRef(p/n)
            case _ => fail("open module cannot own expressions other than identifiers")(o)
          }
        }
      }
    case _ => None
  }

  def inferOperator(gc: GlobalContext,op: Operator,ins: List[Type])(implicit cause: Expression): Type = {
    val param = Type.unknown(gc)
    val possibleTypes = op.types:::op.polyTypes(param)
    val matchResults = possibleTypes.map {f =>
      matchTypes(ProdType.simple(ins), ProdType.simple(f.simpleInputs), BiContext(Nil))(gc,Some(true)).map((f,_))
    }
    val matchingTypes = matchResults.flatMap(_.toList)
    if (matchingTypes.length == 0)
      fail("ill-typed operator")
    val outs = Util.distinct(matchingTypes.map(_._1.out))
    // infer return type if all possible types agree
    val out = if (outs.length == 1) outs.head else
      fail("cannot disambiguate operator")
    // find all unknowns that all possible types agree on
    var commonAssignments: TypeAssignments = matchingTypes.head._2
    matchingTypes.tail.foreach {case (_,next) => commonAssignments = commonAssignments intersect next}
    // if we found multiple assignments for the parameter of this operator, take their union
    val (paramAssignments, otherAssignments) = commonAssignments.partition(_._1 == param)
    val paramAssignment = if (paramAssignments.isEmpty) Nil
      else {
        val u = typeUnion(gc, paramAssignments.map(_._2))
        if (u == AnyType) fail("incompatible operator arguments")
        List((param, u))
      }
    // better take union than fail because of equality and operations on collections
    assignAsMatched(paramAssignment:::otherAssignments)
    out
  }

  private type TypeAssignments = List[(UnknownType,Type)]
  /** checks if two types can be made equal by assigning to unknowns, returns those assignments
    * @param rens alpha-renaming of the variables in a, b (additional to the ones from gc) relative to which the types match
    *             renames from b to a
    * @param subTypeDirection Some(true): allow a <: b; Some(false): allow b <: a
    * @param gc the context of a and b
    */
  private def matchTypes(a: Type, b: Type, cons: BiContext)
                        (implicit gc: GlobalContext, subTypeDirection: Option[Boolean]): Option[TypeAssignments] = {
    val aK = a.skipUnknown
    val bK = b.skipUnknown
    (aK,bK) match {
      case (_:ClosedRef | _:OpenRef | _: BaseType | _: ClassType | _: ExprsOver, _) if aK == bK =>
        // trivial cases first for speed
        Some(Nil)
      case (u: UnknownType, v: UnknownType) if u.container == v.container =>
        // avoid solving an unknown by itself
        val sub = cons.renameRightToLeft
        val argsComp = (u.sub.decls zip v.sub.decls).forall {case (r,s) => r.dfO.get == s.dfO.get.substitute(sub)}
        if (argsComp) Some(Nil) else None
      // solve
      case (u: UnknownType, k) if u.isSolvable =>
        solveType(gc,cons,u,k,true)
      case (k, u: UnknownType) if k.known && u.isSolvable =>
        solveType(gc,cons,u,k,false)
      // recursive cases
      /** case (NumberType(k), NumberType(l)) =>
        if (k == l ||
          (subTypeDirection.contains(true)  && (k sub l).contains(true)) ||
          (subTypeDirection.contains(false) && (l sub k).contains(true))
        ) Some(List())
        else None */
      case _ if aK.getClass != bK.getClass => None // fail quickly
      case (ProdType(as), ProdType(bs)) => matchTypeLists(as,bs,cons,false)
      case (FunType(as,c), FunType(bs,d)) =>
        val asc = as.append(VarDecl.anonymous(c))
        val bsd = bs.append(VarDecl.anonymous(d))
        matchTypeLists(asc,bsd,cons,true)
      case (CollectionType(c,k), CollectionType(d,l)) =>
        if (k == l || (subTypeDirection.contains(true) && (k sub l)) || (subTypeDirection.contains(false) && (l sub k)))
          matchTypes(c,d,cons)
        else
          None
      case _ =>
        if (aK == bK.substitute(cons.renameRightToLeft)) Some(Nil) else None
    }
  }

  /** pre: u.solvable */
  private def solveType(gc: GlobalContext, cons: BiContext, u: UnknownType, k: Type, uOnLeft: Boolean): Option[TypeAssignments] = {
    // val (l,r) = (gc.append(cons.left), gc.append(cons.right)
    // val (uCon,kCon) = if (uOnLeft) (l,r) else (r,l)
    // now: gc |- kSub: kCon -> uCon
    //      gc, kCon |- k
    //      gc, uCon |- u = ??? [u.sub]
    // to match, use
    //      gc, uCon |- u = kS    <=>   ??? = kS[u.sub.inverse]
    val uSubInv = u.sub.inverse.get // defined by precondition
    val patternArgs = uSubInv.decls.map(_.name)
    val kSub = if (uOnLeft) cons.renameRightToLeft else cons.renameLeftToRight
    val kS = Substituter(gc, kSub, k)
    val kfvs = FreeVariables.collect(kS)
    if (!Util.sub(kfvs, patternArgs)) {
      return None // kS references variables not allowed in u; some callers would even want an error here
    }
    val sol = kS.substitute(uSubInv)
    Some(List((u,sol)))
  }

  private def matchTypeLists(as: LocalContext, bs: LocalContext, cons: BiContext, flipSubtypingExceptLast: Boolean)
                            (implicit gc: GlobalContext, subTypeDirection: Option[Boolean]): Option[TypeAssignments] = {
    if (as.length != bs.length) return None
    var ms: TypeAssignments = Nil
    var consI = cons
    var i = 0
    val last = as.length
    (as.decls zip bs.decls).reverse.map {case (a,b) =>
      i += 1
      val std = if (i != last && flipSubtypingExceptLast) subTypeDirection.map(!_) else subTypeDirection
      matchTypes(a.tp, b.tp, consI)(gc, std) match {
        case Some(m) =>
          if (!a.anonymous && !b.anonymous) consI = consI.append(a,b)
          else if (a.anonymous && b.anonymous) {
            // no need to remember variable in simple types
          } else {
            return None // a simple type could match a dependent one, but we can worry about that later
          }
          ms = m ::: ms
        case None => return None
      }
    }
    Some(ms)
  }
  /** applies assignments returned by matchTypes */
  private def assignAsMatched(as: TypeAssignments) = {
    Util.distinct(as).foreach {case (u,a) =>
      u.set(a)
    }
  }
  /** like matchTypes, but makes the assignments right away if matching is possible */
  private def equateTypes(gc: GlobalContext, a: Type, b: Type)(subTypeDir: Option[Boolean]) = {
    matchTypes(a,b,BiContext(Nil))(gc, subTypeDir) match {
      case Some(uas) => assignAsMatched(uas); true
      case None => false
    }
  }
}

class MagicFunctions(gc: GlobalContext) {
  class MagicFunction(name: String) {
    def insert(dom: Theory, owner: Expression, args: List[Expression]) = Application(owner.field(dom,name),args)
    def unapply(tp: Type) = tp match {
      case ClassType(thy) => gc.push(thy).lookupRegional(name) match {
        case Some(d: ExprDecl) => Some((thy,d.tp))
        case _ => None
      }
      case _ => None
    }
  }
  object asstring extends MagicFunction("toString")
  object listElement extends MagicFunction("elemAt")
  object iteration extends MagicFunction("elements")
  object application extends MagicFunction("apply")
  class projection(n: Int) extends MagicFunction("component_"+n)
  object evaluation extends MagicFunction("eval")
}
object MagicFunctions {
  val asType = "univ"
  def typeOf(e: Expression, dom: Theory) = OwnedType(e,dom, ClosedRef(asType))
}