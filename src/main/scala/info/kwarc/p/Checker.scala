package info.kwarc.p

import SyntaxFragment.matchC

import Checker._

// TODO: pure computations during checking (maybe: rewriting as a special case of matching; maybe rewriting on user-declared types)

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

  def checkVocabulary(gc: GlobalContext, voc: TheoryValue, keepFull: Boolean)(implicit cause: SyntaxFragment) = {
    voc.decls.foreach {d => d.global = true}
    val dsC = flattenCheckDeclarations(gc, voc.decls, FlattenParams(alsoCheck=true, mustBeConcrete=false, keepFull))
    TheoryValue(dsC).copyFrom(voc)
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
        val envM = gc.add(m.copy(df = Theory.empty).copyFrom(m)).enter(m)
        if (!m.closed) {
          m.decls.foreach {_.global = true}
        }
        val kf = true
        val declsC = flattenCheckDeclarations(envM, m.decls, FlattenParams(alsoCheck=true, mustBeConcrete=false, keepFull=kf))
        m.copy(df = Theory(declsC, Some(kf)))
        // TODO instance creation may occur before or while a theory is checked - needs 2-phase approach
      case id: Include =>
        if (id.dom != null) {
          val domC = checkTheory(gc, id.dom)(id)
          // TODO: what about includes of open theories
          val dfOC = id.dfO map {d => checkExpression(gc,d,ClassType(domC))}
          Include(domC,dfOC,id.realize)
        } else id.dfO match {
          case None => fail("untyped include")
          case Some(df) =>
            // infer domain from definiens
            val (dfC,dfI) = inferExpression(gc,df)(true)
            PurityChecker(gc,dfC)
            dfI match {
              case ClassType(thy) => Include(thy, Some(dfC), id.realize)
              case _ => fail("definiens of include must be an instance")
            }
        }
      case sd: SymbolDeclaration =>
        checkSymbolDeclaration(gc, sd)
        // purity checks?
    }
    declC.copyFrom(decl)
  }

  /** modifies the behavior of flattening theories below
    * - alsoCheck: the input declarations are also checked; all realizations are checked at the end
    * - mustBeConcrete: all symbol declarations must be defined at the end
    * - keepFull: all non-subsumed declarations are in the result vs. only the subsuming ones and includes
    */
  private case class FlattenParams(alsoCheck: Boolean, mustBeConcrete: Boolean, keepFull: Boolean)
  private case class FlattenInput(decls: List[Declaration], alsoCheck: Boolean, include: Option[Include]) {
    def tail = copy(decls = decls.tail)
    def alsoTranslate = include.flatMap(_.dfO)
  }
  /** checking and flattening a list of declarations
      - symbol declarations: keep, possibly merge/clash with existing declaration
      - include T [=m]: keep, possibly merge/clash,
        then also add flat body of T [changing all declarations d to be owned by m]
        this causes an exponential blow-up, but that is acceptable because
        - unrefined declarations are not copied
        - refinements by defined includes only need a shallow copy of the declaration; pushing the owner inwards is lazy

     Any two declarations for the same name get merged as follows:
     - A subsumed declarations is marked and removed at the end.
     - If a new declaration has to be generated, it is added and both refinees are marked as subsumed.
     - Subsuming declarations are marked as well.
    */
  private def flattenCheckDeclarations(gc: GlobalContext, decls: List[Declaration], pars: FlattenParams)
                                      (implicit cause: SyntaxFragment): List[Declaration] = {
    // ***** state and initialization *****
    /* a FIFO queue of lists of declarations that must be flattened
     * Later on included lists of declarations will be prefixed with that flag negated and the definiens of the include.
     * It would be equivalent to keep a List[Declaration] instead of what is essentially a list of lists of declarations
     * if the former always holds the concatenation of the latter.
     * But our implementation is more efficient because it avoids that copying lists.
     */
    // initially, we need to flatten the original list, which must be checked but not translated
    // we mark them as subsuming so that they are kept (even if they do not subsume anything)
    decls.foreach(_.subsuming = true)
    var todo = List(FlattenInput(decls,pars.alsoCheck,None))
    val numPriorDecls = gc.parentDecls.length // new declarations are appended to these
    var gcC = gc // will change as we process declarations
    var mustDefine: List[String] = Nil // symbols for which definedness must be checked at the end
    var doesDefine: List[String] = Nil // symbols for which definitions are present
    // ***** flattening *****
    // repeat until no todos are left (skipping empty todos)
    while ({todo = todo.dropWhile(_.decls.isEmpty); todo.nonEmpty}) {
      // take off the first among the todos
      val current = todo.head
      val d = current.decls.head
      todo = current.tail :: todo.tail
      // check it if necessary (already merges with declarations of the same name that are already present)
      val dC = if (current.alsoCheck) checkDeclaration(gcC, d) else d
      // translate if necessary
      val dT = current.include match {
        case None => dC
        case Some(incl) => incl.dfO match {
          case None => dC
          case Some(df) =>
            // translate
            val dS = OwnersSubstitutor.applyDecl(gcC.push(incl.dom,Some(df)),dC,1)
            // add definiens if none yet
            dS match {
              case ed: ExprDecl if !ed.defined => ed.copy(dfO = Some(OwnedExpr(df,incl.dom,ed.toRef)))
              case td: TypeDecl if !td.defined => td.copy(dfO = Some(OwnedType(df,incl.dom,td.toRef)))
              case id: Include if !id.defined => id.copy(realize = false,dfO = Some(df))
              case _ => dS
            }
        }
      }
      // shared code for adding a new sym decl
      def add(sd: SymbolDeclaration): Unit = {
        gcC = gcC.add(sd)
        // track if the declaration has or needs a definition
        if (sd.defined) {
          doesDefine ::= sd.name
        } else if (pars.alsoCheck && (pars.mustBeConcrete || current.include.exists(_.realize)))
          mustDefine ::= sd.name
      }
      // compare with compatible existing declaration and merge if any; otherwise add
      dT match {
        case nw: Include =>
          /* Adding a redundant include is harmless because the declaration merging will absorb the redundant declarations.
             But it is inefficient. So we apply sufficient criteria to skip redundant includes. */
          val existing = gcC.parentDecls.collectFirst {
            case old: Include if old.dom == nw.dom => old
          }
          val added = existing match {
            case None =>
              gcC = gcC.add(nw)
              true
            case Some(old) =>
              if (!nw.total) {
                // a new plain include is subsumed by any old include
                false
              } else if (nw.actualRealize && old.total) {
                // a new realizing include is subsumed by an old total one
                false
              } else if (nw.defined && old.defined) {
                // if both are defined, it's either redundant or an error (realizations don't matter)
                if (nw.dfO != old.dfO) {
                  reportError(s"definitions of includes not compatible")(nw)
                }
                false
              } else {
                // now nw.defined && !old.defined: add
                // or nw.actualRealize && !old.total: also add, but actually it would suffice to set must-define
                old.subsumed = true
                nw.subsuming = true
                gcC = gcC.add(nw)
                true
              }
          }
          // if it is a non-redundant include, queue the body as well (depth-first traversal of the include tree)
          if (added) {
            // check if the included declarations must be realized
            val isRealize = current.include match {
              case None => nw.actualRealize
              case Some(c) => c.actualRealize && !nw.total // composed include is only realization when non-total composed with realize
            }
            // queue the included declarations
            if (nw.dom.isInstanceOf[TheoryValue]) nw.subsumed = true // no need to keep trivial includes
            val domE = evaluateTheory(gcC, nw.dom)
            todo ::= FlattenInput(domE.decls, false, Some(nw.copy(realize = isRealize)))
          }
        case nw: NamedDeclaration =>
          val existing = gcC.parentDecls.find {e => e.nameO contains nw.name}
          existing match {
            case None =>
              // new declaration is new: add
              if (debug) println("new declaration: " + nw)
              nw match {
                case sd: SymbolDeclaration => add(sd)
                case _ => gcC = gcC.add(nw)
              }
            case Some(old) =>
              (old, nw) match {
                case (o, n) if o.kind != n.kind =>
                  // new declaration clashes: error
                  reportError(s"declarations for ${nw.name} not compatible")
                case (o, n) if o == n =>
                // new module is redundant: skip (optimization for the common case of copies of declarations)
                case (old: Module, nw: Module) =>
                  if (old.closed != nw.closed) {
                    reportError(s"modules for ${nw.name} of different openness")
                  } else if (old.df != nw.df) {
                    // TODO: merge bodies
                    reportError(s"declaration for ${nw.name} already exists")
                  } else {
                    // new module is redundant: skip
                  }
                case (old: SymbolDeclaration, nw: SymbolDeclaration) =>
                  // now nw of the same name/kind as old
                  val comp = Compare(gcC, old, nw)
                  comp match {
                    case Compare.Identical =>
                      // new declaration is copy: nothing to do
                      if (debug) println("duplicate declaration: " + nw)
                    case Compare.Subsumes =>
                      // new declaration is redundant: nothing to do but remember
                      if (debug) println("subsumed declaration: " + nw)
                    case Compare.SubsumedBy =>
                      // old declaration is redundant: mark it for later removal and add the new one
                      old.subsumed = true
                      nw.subsuming = true
                      if (debug) println("subsuming declaration: " + nw)
                      add(nw)
                    case Compare.Merged(tM, dM) =>
                      val merged = nw match {
                        // TODO merges that involve mutable fields
                        case ed: ExprDecl => ExprDecl(nw.name, tM, dM.asInstanceOf[Option[Expression]], ed.mutable)
                        case td: TypeDecl => TypeDecl(nw.name, tM, dM.asInstanceOf[Option[Type]])
                      }
                      old.subsumed = true
                      merged.subsuming = true
                      add(merged.copyFrom(nw)) // nw is more likely to have the definition
                    case Compare.Clashing =>
                      // declarations incompatible; further comparison needed
                      reportError("declaration clash")(nw)
                  }
                case _ => throw IError("unexpected declarations")
              }
          }
      }
    } // end while
    // ***** finalization *****
    /* newDecls is the list of newly added declarations in reverse order
       We still have to reverse it, drop all subsumed declarations, and perform final checks. */
    val totalDecls = gcC.parentDecls
    val newDecls = totalDecls.take(totalDecls.length-numPriorDecls)
    var result: List[Declaration] = Nil // the eventual result
    newDecls.foreach {d =>
      // decide if d must be kept in the result; in particular, drop subsumed declarations
      if (!d.subsumed && (pars.keepFull || d.subsuming || d.isInstanceOf[Include])) {
        result ::= d
      }
      // reset flags to avoid messing up the state in included modules (which share a pointer with d if unchanged)
      // The pointer sharing is a problem if we ever have multiple threads checking the same AST
      d.subsumed = false
      d.subsuming = false
    }
    // totality check (if requested)
    if (pars.alsoCheck) {
      val missingDefinitions = mustDefine.filterNot(doesDefine.contains)
      missingDefinitions.foreach {n => reportError("missing definition of " + n)}
    }
    // return the result
    result
  }

  private object Compare {
    sealed abstract class Result
    case object Identical extends Result
    case object Subsumes extends Result
    case object SubsumedBy extends Result
    case class Merged(tp: Type, df: Option[Object]) extends Result
    case object Clashing extends Result

    /** tries to merge two symbol declarations
      * pre: same name, same kind
      */
    def apply(gc: GlobalContext, sd1: SymbolDeclaration, sd2: SymbolDeclaration): Result = {
      if (sd1 == sd2) return Identical
      // compare type (bound) and definiens separately
      val tpComp = compareTT(gc, sd1.tp, sd2.tp)
      val dfComp = compareOO(sd1.dfO, sd2.dfO)
      (tpComp, dfComp) match {
        // either clashes
        case (Clashing, _) | (_, Clashing) => Clashing
        // both identical
        case (Identical, Identical) => Identical
        // both at least subsume
        case ((Identical|Subsumes), (Identical|Subsumes)) => Subsumes
        // both at least subsumed by
        case ((Identical|SubsumedBy), (Identical|SubsumedBy)) => SubsumedBy
        // both subsume but in different directions
        case (Subsumes, SubsumedBy) | (SubsumedBy, Subsumes) =>
          val (tpM, dfM) = if (tpComp == Subsumes) (sd1.tp, sd2.dfO.get) else (sd2.tp, sd1.dfO.get)
          // definiens must be checked against now-tighter type
          checkTypeOrExpression(gc, dfM, tpM)(dfM)
          Merged(tpM, Some(dfM))
        // types merged, definitions compatible
        case (Merged(tpM, _), _) =>
          val dfOM = sd1.dfO orElse sd2.dfO
          dfOM.foreach {dfM =>
            // definiens must be checked against now-tighter type
            // if both defs are present, this should be redundant, but we do it anyway to account for approximate intersection types
            checkTypeOrExpression(gc, dfM, tpM)(dfM)
          }
          Merged(tpM, dfOM)
        case _ => throw IError("unexpected comparison case")
      }
    }
    def compareTT(gc: GlobalContext, t1: Type, t2: Type): Result = {
      if (t1 == t2) return Identical
      val t1N = Normalize(gc,t1)
      val t2N = Normalize(gc,t2)
      if (t1N == t2N) Identical else {
        val tI = typeIntersection(gc, t1N, t2N)
        if (tI == EmptyType) Clashing
        else if (tI == t1) Subsumes
        else if (tI == t2) SubsumedBy
        else Merged(tI,None)
      }
    }
    def compareOO(o1: Option[Object], o2: Option[Object]): Result =
      (o1, o2) match {
        case (Some(_), None)    => Subsumes
        case (None, Some(_))    => SubsumedBy
        case (Some(x), Some(y)) => if (x == y) Identical else Clashing
        case (None, None)       => Identical
      }
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
        if (abs.dfO.isDefined && abs.dfO != sd.dfO) reportError("name is inherited and already defined differently")
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

  /** checks a theory, preserving its structure */
  def checkTheory(gc: GlobalContext, thy: Theory, mustBeConcrete: Boolean = false)(implicit cause: SyntaxFragment): Theory = {
    if (thy.isFlat) return thy
    thy match {
      case thy: TheoryValue =>
        val kf = false
        val declsC = flattenCheckDeclarations(gc.enterEmpty(),thy.decls,FlattenParams(alsoCheck=true,mustBeConcrete,keepFull=kf))
        Theory(declsC, Some(kf))
      case r: Ref =>
        val (rC,ndO) = gc.resolveName(r).getOrElse(fail("unknown identifier"))
        val nd = ndO.getOrElse(gc.lookupModule(r))
        (rC,nd) match {
          case (rC: Ref,m: Module) =>
            if (!m.closed) fail("module not closed")
            val undef = m.df.undefined
            // realizations were already checked when checking r
            if (mustBeConcrete && undef.nonEmpty) fail("theory not concrete, missing definitions for: " + undef.map(_.name).mkString(", "))
            rC.flatness = Theory.QuasiFlat // tentatively trying to avoid expanding references
            rC
          case _ => fail("identifier not a module")
        }
      case OwnedTheory(owner,dom,t) =>
        // owning a theory does not affect, definedness of fields; so no definedness checks needed here
        val (ownerC,ownerI) = inferExpressionNorm(gc,owner)(true)
        PurityChecker(ownerC)(gc,())
        ownerI match {
          case ClassType(domC) =>
            if (dom != null && dom != domC) reportError("unexpected theory")
            val gcD = gc.push(domC,Some(ownerC))
            val tC = checkTheory(gcD,t,mustBeConcrete)
            OwnedTheory(ownerC,domC,tC)
          case _ => fail("owner must be an instance")
        }
    }
  }

  /** tests equality of theories quickly; returns None if inclonclusive */
  def tryCheckTheoryEqual(gc: GlobalContext, a: Theory, b: Theory): Option[Boolean] = {
    if (a == b) return Some(true)
    val aE = evaluateTheory(gc, a)
    val bE = evaluateTheory(gc, b)
    if (a == b) return Some(true)
    None
  }

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
    * pre: same length, no definitions
    * TODO substitution into union context is not well-formed; every argument must be checked individually
    */
  def typesUnionOrIntersection(union: Boolean)
                              (gc: GlobalContext, as: LocalContext, bs: LocalContext): Option[(LocalContext,Substitution)] = {
    // fail("wrong number of components: " + expected(as.length.toString,bs.length.toString))
    if (as.length != bs.length) return None
    var gcI = gc
    var subI = Substitution.empty
    var abs = LocalContext.empty
    (as.decls.reverse zip bs.decls.reverse).foreach {case (a,b) =>
      if (a.defined || b.defined) return None //reportError("union with defined variables")
      val bS = Substituter(gcI, subI, b.tp)
      val ab = if (union) typeUnion(gcI, a.tp, bS) else typeIntersection(gcI, a.tp, bS)
      val vd = VarDecl(a.name, ab)
      abs = abs append vd
      gcI = gcI append vd
      subI = subI.appendRename(b.name, vd)
    }
    Some((abs,subI))
  }


  /** theory a subsumbed by b */
  def checkSubtheory(gc: GlobalContext, a: Theory, b: Theory)(implicit cause: SyntaxFragment): Unit = {
    // we apply sufficient criteria first, in order of efficiency
    // identical
    if (a == b) return
    val bE = evaluateTheory(gc, b)
    val bEDecls = bE.decls
    // "include a" part of bE
    if (!a.isInstanceOf[TheoryValue] && a.decls.forall(bEDecls.contains)) return
    val aE = evaluateTheory(gc, a)
    val skipIncludes = aE.flatness == Theory.FullyFlat
    // check if all declarations of aE are subsumed by a declaration in bE
    def notAmong(ds: List[Declaration]) =
      aE.decls.filterNot(c => (skipIncludes && c.isInstanceOf[Include]) || ds.exists(d => c.subsumedBy(d)))
    if (notAmong(bEDecls).isEmpty) return
    val bN = Normalize(gc, b)
    val missing = notAmong(bN.decls)
    if (missing.isEmpty) return
    def giveUp(msg: String) = {
      reportError(s"theory not included:\nsub:    $a\nsuper:  $b\nreason: $msg\n")
    }
    // eventually: check in depth
    missing.foreach {
      case m: SymbolDeclaration =>
        val gcB = gc.push(bN)
        gcB.lookupRegional(m.name) match {
          case None => giveUp(s"no declaration for ${m.name}")
          case Some(p) => checkSubsumedBy(gcB,m,p)
        }
      case m => giveUp("not subsumed: " + m)
    }
  }

  def checkSubsumedBy(gc: GlobalContext, a: Declaration, b: Declaration)(implicit cause: SyntaxFragment): Unit = {
    if (a == b) return
    if (!a.similar(b))
      reportError("declaration not similar: " + b)
    if (a.subsumedBy(b)) return
    (a,b) match {
      case (a: SymbolDeclaration, b: SymbolDeclaration) =>
        checkSubtype(gc, b.tp, a.tp)
        (a.dfO,b.dfO) match {
          case (None,_) =>
          case (Some(_),None) => reportError(s"missing definition for${a.name}\n$a\n$b")
          case (Some(aD:Expression), Some(bD:Expression)) =>
            if (aD != bD) reportError(s"clashing definitions for ${a.name}\n$a\n$b")
          case (Some(aD: Type), Some(bD: Type)) =>
            checkEqualType(gc,aD,bD)
          case _ => throw IError("unexpected definition types")
        }
      case _ => reportError("incompatible declarations")
    }
  }

  // ***************** Types **************************************
  /** checks an expression against a type, or a type against a bound */
  def checkTypeOrExpression(gc: GlobalContext, o: Object, tp: Type)(cause: SyntaxFragment): Unit = o match {
    case e: Expression => checkExpression(gc, e, tp)
    case t: Type => checkSubtype(gc, t, tp)(o)
    case th: Theory => throw IError("cannot check theory against type")
  }

  def checkType(gc: GlobalContext, tp: Type, bound: Type): Type = {
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
        val sd = sdO.getOrElse(fail("identifier not a symbol"))
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
            // module ref, interpret as class type, closed ref not supported yet
            // if (!m.closed) reportError("open module not a type")
            checkType(gc, ClassType(rC))
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
        val qC = checkType(gc.pushQuoted(scC),q)
        ExprsOver(scC,qC)
      case ProofType(f) =>
        val fC = checkExpressionPure(gc,f,BoolType)
        ProofType(fC)
      case u: UnknownType =>
        if (u.known) {
          checkType(gc,u.skipUnknown)
        } else {
          if (u.originalContext != null && u.sub != null) {
            u // introduced during checking
          } else if (u.originalContext != null || u.sub != null) {
            throw IError("unexpected context in unknown type") // never happens anyway
          } else {
            UnknownType(gc,u.container,gc.visibleLocals.identity) // set up for later inference
          }
        }
    }
  }

  def checkEqualType(gc: GlobalContext, a: Type, b: Type)(implicit cause: SyntaxFragment): Unit = {
    if (a == b) return
    val aN = Normalize(gc,a)
    val bN = Normalize(gc,b)
    if (aN != bN) reportError(s"types not equal\n$a\n$b")
  }

  /** a <: b
   *  force: solve variables, raise error if fail, return Some(true)
   *  !force: no side effect, return None if inconclusive
   */
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
      case (ClassType(aT),ClassType(bT)) =>
        // model of aT or model of bT, i.e., model of intersection
        checkSubtheory(gc,bT,aT) // larger theory = smaller type
      case (OwnedType(o,d,s),OwnedType(p,_,t)) if o == p =>
        checkSubtype(gc.push(d,Some(o)), s, t)
      case (ExprsOver(aT,u),ExprsOver(bT,v)) =>
        checkSubtheory(gc,aT,bT)
        checkSubtype(gc.pushQuoted(aT),u,v)
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
  def typeUnion(gc: GlobalContext,tps: List[Type]): Type = {
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
  def typeUnion(gc: GlobalContext,a: Type,b: Type): Type = {
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
      case (ProdType(as),ProdType(bs)) if as.length == bs.length =>
        typesUnionOrIntersection(true)(gc,as,bs) match {
          case Some((abs,_)) => ProdType(abs)
          case None => AnyType
        }
      case (FunType(as,o),FunType(bs,p)) if as.length == bs.length =>
        typesUnionOrIntersection(false)(gc, as, bs) match {
          case Some((abs, sub)) =>
            val gcI = gc.append(abs)
            val pS = Substituter(gcI, sub, p)
            val op = typeUnion(gcI, o, pS)
            FunType(abs, op)
          case None => AnyType
        }
      case (ExprsOver(aT,u), ExprsOver(bT, v)) =>
        val thyU = theoryUnion(gc, aT, bT)
        // aT-expression of type u or bT-expression of type v, i.e., expression over union of union type
        ExprsOver(thyU, typeUnion(gc.pushQuoted(thyU), u, v))
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
  def typeIntersection(gc: GlobalContext, a: Type, b: Type): Type = {
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
        typesUnionOrIntersection(false)(gc,as,bs) match {
          case Some((abs,_)) => ProdType(abs)
          case None => EmptyType
        }
      case (FunType(as,o),FunType(bs,p)) if as.length == bs.length =>
        typesUnionOrIntersection(true)(gc,as,bs) match {
          case Some((abs,sub)) =>
            val gcI = gc.append(abs)
            val pS = Substituter(gcI,sub,p)
            val op = typeIntersection(gcI,o,pS)
            FunType(abs,op)
          case None => EmptyType
        }
      case (ExprsOver(aT,u), ExprsOver(bT, v)) =>
        // aT-expression of type u and bT-expression of type v, i.e., expression over the intersection of intersection type
        val thyI = theoryIntersection(gc, aT, bT)
        val thyU = theoryUnion(gc, aT, bT)
        ExprsOver(thyI, typeIntersection(gc.pushQuoted(thyU), u, v))
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
    if (a.isEmpty) return b
    if (b.isEmpty) return a
    if (a == b) return a
    val thy = Theory(a.decls:::b.decls)
    val declsF = flattenCheckDeclarations(gc.enterEmpty(), thy.decls, FlattenParams(false,false,false))(thy)
    // thy.isFlat = a.isFlat && b.isFlat
    TheoryValue(declsF)
  }

  /** intersection of theories: the union of all common includes */
  def theoryIntersection(gc: GlobalContext, a: Theory, b: Theory): Theory = {
    val pqs = a.decls intersect b.decls // TODO remove definiens if not the same
    val thy = Theory(pqs)
    thy
  }

  /** normalizes a type: definitions expanded, flattened */
  object Normalize extends StatelessTraverser {
    override def apply(thy: Theory)(implicit gc: GlobalContext, a:Unit): Theory = {
      // possible infinite loop if keepFull==true
      if (thy.isFlat) return thy
      val kf = true
      val pars = FlattenParams(alsoCheck=false, mustBeConcrete=false, keepFull=kf)
      val declsF = flattenCheckDeclarations(gc.enterEmpty(),thy.decls,pars)
      Theory(declsF, Some(kf))
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
        case OwnedType(own,dom,t) =>
          // we must reinfer the domain because the fields in the cached domain may have acquired definitions
          // when the object was moved into another region
          // TODO this code should go, and the issues solved elsewhere
          val ownI = inferCheckedExpression(gc,own) match {
            case ct:ClassType => ct
            case t => apply(t)
          }
          val dom = ownI match {
            case ClassType(d) => d
            case _ => throw IError("unexpected type")
          }
          val gcI = gc.push(dom,Some(own))
          val tN = apply(gcI, t)
          val tpN = OwnersSubstitutor.applyType(gcI,tN)
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
      case (CollectionValue(es,vk), CollectionType(t,tk)) =>
        if (!vk.sub(tk)) reportError(s"a $vk cannot be seen as a $tk")
        if (vk.sizeOne && es.length > 1) reportError("option value must have at most one element")
        val esC = es.map(e => checkExpression(gc,e,t))
        CollectionValue(esC, tk)
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
        val instC = checkTheory(gc, Theory(Include(thyB) :: thyA.decls), true)
        Instance(instC)
      case (ExprOver(scE,e), ExprsOver(scT, tp)) =>
        val scTC = checkTheory(gc, scT)
        if (scE != null) {
          checkSubtheory(gc, scE, scTC)
        }
        val eC = checkExpression(gc.pushQuoted(scTC), e, tp)
        ExprOver(scTC, eC)
      case (Eval(q), a) =>
        val qC = checkExpression(gc.pop(), q, ExprsOver(gc.theory, a))
        Eval(qC)
      case (Application(op: BaseOperator,args),_) if !op.tp.known && op.operator.isCheckable =>
        val (argsC,argsI) = args.map(a => inferExpressionNorm(gc,a)(true)).unzip
        val opTp = SimpleFunType(argsI,tpN)
        val opC = checkExpression(gc,op,opTp)
        Application(opC,argsC)
      case (BaseOperator(op,opTp),ft:FunType) if op.isCheckable =>
          opTp.skipUnknown match {
            case u: UnknownType =>
              if (!ft.simple) reportError("operators cannot have dependent type")
              if (u.originalContext != null || u.sub != null) throw IError("unexpected context in unknown operator type")
              val outI = inferOperator(gc, op, ft.simpleInputs)
              checkSubtype(gc, outI, ft.out)
              u.set(ft) // just in case this unknown was referenced elsewhere
            case _ =>
              checkSubtype(gc, opTp, ft)
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
      case (UndefinedValue(a), b) =>
        val aC = checkType(gc,a,b)
        UndefinedValue(aC)
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
  def checkExpressionPattern(gc: GlobalContext, e: Expression, tp: Type): (LocalContext,Expression) = {
    // TODO: this interprets any name bound in the context as a constant pattern, rather than shadowing it
    disambiguateOwnedObject(gc, e).foreach {corrected => return checkExpressionPattern(gc, corrected, tp)}
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
      case e: BaseValue => (e, e.tp)
      case op: BaseOperator =>
        if (!op.tp.known) {
          reportError("cannot infer type of operator")
        }
        val ft = Normalize(gc, op.tp) match {
          case ft: FunType if ft.simple => ft
          case _ => fail("operator type not a simple function")
        }
        val out = inferOperator(gc, op.operator, ft.simpleInputs)
        if (alsoCheck)
          checkSubtype(gc, out, ft.out)(exp)
        (BaseOperator(op.operator, ft), op.tp)
      case r: OpenRef =>
        val (rC, rd) = sdCached match {
          case Some(d) => (r, d)
          case _ => checkOpenRef(gc, r)
        }
        rd match {
          case ed: ExprDecl => (rC, ed.tp)
          case _ => fail(s"$rC is not an expression")
        }
      case ClosedRef(n) =>
        sdCached match {
          case Some(ed: ExprDecl) => (exp, ed.tp)
          case _ => fail("not an expression")
        }
      case This(l) =>
        if (l <= 0) fail("illegal level")
        if (gc.regions.length < l) fail("level does not exist")
        val (skipped, rest) = gc.regions.splitAt(l - 1)
        val reg = rest.head
        if (skipped.exists(!_.transparent))
          fail("level is not accessible")
        reg.physical match {
          case Some(false) => fail("parent is not a closed theory")
          case _ =>
            val thy = reg.region.theory
            val thyS = OwnersSubstitutor.applyTheory(gc, reg.region.theory, -(l - 1))
            (exp, ClassType(thyS))
        }
      case OwnedExpr(owner, dom, e) =>
        val (ownerC, ownerI) = if (alsoCheck) inferExpressionNorm(gc, owner) else (owner, ClassType(dom))
        ownerI match {
          case ClassType(domC) =>
            if (alsoCheck)
              if (dom != null && dom != domC) fail("unexpected given theory")
            val envO = gc.push(domC, Some(ownerC))
            val (eC, eI) = inferExpression(envO, e)
            (OwnedExpr(ownerC, domC, eC), OwnedType(ownerC, domC, eI))
          case _ => fail("owner must be an instance")
        }
      case VarRef(n) =>
        val vd = gc.lookupLocal(n).getOrElse {
          fail("undeclared variables")
        }
        (exp, vd.tp)
      case Instance(thy) =>
        val thyC = if (!alsoCheck) thy else checkTheory(gc, thy, true)
        (Instance(thyC), ClassType(thyC))
      case ExprOver(sc, q) =>
        val scC = if (alsoCheck) checkTheory(gc, sc) else sc
        val (qC, qI) = inferExpression(gc.pushQuoted(scC), q)
        (ExprOver(scC, qC), ExprsOver(scC, qI))
      case Eval(e) =>
        if (alsoCheck)
          if (gc.regions.isEmpty) fail("eval outside quotation")
        val (eC, eI) = inferExpressionNorm(gc.pop(), e)
        eI match {
          case ExprsOver(eT, q) =>
            if (alsoCheck) {
              checkSubtheory(gc, eT, gc.theory)
            }
            (Eval(eC), q)
          case mf.evaluation(dom, a) =>
            (mf.evaluation.insert(dom, eC, Nil), a)
          case _ => fail("not a quoted expression")
        }
      case MatchCase(ctx, p, b) =>
        fail("match case outside of match")
      case Lambda(ins, bd, mr) =>
        val insC = if (alsoCheck) checkLocal(gc, ins, false, false) else ins
        val (bdC, bdI) = inferExpression(gc.append(insC), bd)
        (Lambda(insC, bdC, mr), FunType(insC, bdI))
      case Application(f, as) =>
        f match {
          case op: BaseOperator if op.operator.isPseudo =>
            val pop = op.operator
            pop match {
              case Equal | Inequal =>
                if (as.length != 2) fail("unexpected number of arguments")
                val expE = Equality(pop == Equal, Type.unknown(gc), as(0), as(1)).copyFrom(exp)
                return inferExpression(gc, expE)
              case _ => fail("unknown pseudo-operator: " + op.operator.symbol)
            }
          case op: BaseOperator if op.operator.isDynamic =>
            val eC = if (alsoCheck) checkDynamicBoolean(gc, exp)._1 else exp
            (eC, BoolType)
          case op: BaseOperator if !op.tp.known =>
            // for an operator of unknown type, we need to infer the argument types first
            val (asC, asI) = as.map(a => inferExpression(gc, a)).unzip
            val out = inferOperator(gc, op.operator, asI)
            val opC = op.copy(tp = SimpleFunType(asI, out))
            (Application(opC, asC), out)
          case f =>
            val (fC, fI) = inferExpressionNorm(gc, f)
            val (fM, ins, out) = fI match {
              case FunType(i, o) => (fC, i, o)
              case ProdType(ys) =>
                as match {
                  case List(IntValue(i)) =>
                    // projections are parsed as applications
                    return inferExpression(gc, Projection(f, i.toInt).copyFrom(exp))
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
                Range(0, as.length).foreach { i =>
                  val vd = VarDecl(n + "_" + i.toString, Type.unknown(gcI))
                  uis = uis append vd
                  gcI = gc append vd
                }
                val uo = Type.unknown(gcI)
                u.set(FunType(uis, uo))
                (fC, uis, uo)
              case mf.application(dom, FunType(i, o)) => (mf.application.insert(dom, fC, as), i, o)
              case _ => fail("not a function")(f)
            }
            if (ins.length != as.length) fail("wrong number of arguments")
            val sub = ins.substitute(as)
            val asC = if (alsoCheck) {
              checkSubstitution(gc, sub, ins)
            } else sub
            val outS = Substituter(gc, asC, out)
            (Application(fM, asC.exprs), outS)
        }
      case Tuple(es) =>
        val (esC, esI) = es.map(e => inferExpression(gc, e)).unzip
        (Tuple(esC), ProdType.simple(esI))
      case Projection(tup, p) =>
        val mfp = new mf.projection(p)
        val (tupC, tupI) = inferExpressionNorm(gc, tup)
        tupI match {
          case ProdType(ts) =>
            if (alsoCheck) {
              if (p <= 0) fail("non-positive index")
              if (p > ts.length) fail("index out of bounds")
            }
            val componentType = ts(p - 1).tp // -1 because components start at 1 but declarations at 0
            val precedingCompDecls = ts.take(p - 1)
            val precedingProjs = Range(1, p).toList.map(i => Projection(tup, i))
            val sub = precedingCompDecls.substitute(precedingProjs)
            val projI = Substituter(gc, sub, componentType)
            (Projection(tupC, p), projI)
          case mfp(dom, a) =>
            (mfp.insert(dom, tupC, List(IntValue(p))), a)
          case _ => fail("not a tuple")
        }
      case CollectionValue(es, k) =>
        val (esC, esI) = es.map(e => inferExpression(gc, e)).unzip
        val eI = typeUnion(gc, esI)
        if (k.sizeOne && es.length > 1) reportError("option value can have at most one element")
        (CollectionValue(esC, k), CollectionType(eI, k))
      case ListElem(l, p) =>
        if (alsoCheck) {
          val u = Type.unknown(gc)
          val lC = checkExpression(gc, l, CollectionType(u, CollectionKind.UList))
          val pC = checkExpression(gc, p, IntType)
          // index bounds not checked
          (ListElem(lC, pC), u)
        } else {
          val (_, CollectionType(a, _)) = inferExpression(gc, l)
          (exp, a)
        }
      case Equality(pos, tp, l, r) =>
        val tpC = if (alsoCheck) checkType(gc, tp) else tp
        val (lC, rC) = if (!alsoCheck) (l, r) else tpC match {
          case u: UnknownType =>
            val (lC, lI) = inferExpression (gc, l)
            val (rC, rI) = inferExpression (gc, r)
            val tpC = typeUnion(gc, lI, rI)
            if (tpC == AnyType) reportError (s"ill-typed equality: $lI, $rI")
            u.set(tpC)
            (lC, rC)
          case _ =>
            (checkExpression(gc, l, tpC), checkExpression(gc, r, tpC))
        }
        (Equality(pos,tpC,lC,rC),BoolType)
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
      case UndefinedValue(a) =>
        val aC = checkType(gc, a)
        (UndefinedValue(aC), aC)
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
          val targets = checkAssignable(gc,e)
          if (!Util.noReps(targets)) fail("multiple assignments to same object")
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
        // condition-bindings are exported to then-branch
        val (condC,condB) = checkDynamicBoolean(gc, cond)
        val (thnC,thnI) = inferExpressionNorm(gc.append(condB), thn)
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

  /** checks a Boolean that may export bindings to sibling expressions
   * parents that want to move bindings from one child to another call this instead of the normal check function
   */
  def checkDynamicBoolean(gc: GlobalContext, b: Expression)(implicit alsoCheck: Boolean): (Expression, LocalContext) = recoverWith((b,LocalContext.empty)) {
    b match {
      case And(l, r) =>
        val (List(lC, rC), lc) = checkDynamicBooleans(gc, List(l, r))
        (And(lC, rC).copyFrom(b), lc)
      case Implies(l, r) =>
        val (List(lC, rC), _) = checkDynamicBooleans(gc, List(l, r))
        (Implies(lC, rC).copyFrom(b), LocalContext.empty)
      case _: VarDecl | _: Assign =>
        // treated as True
        val (bC,_) = inferExpression(gc,b)
        val bB = LocalContext.collectContext(bC)
        (bC, bB)
      case _ =>
        val bC = if (alsoCheck) checkExpression(gc, b, BoolType) else b
        val bB = LocalContext.collectContext(bC)
        (bC, bB)
    }
  }
  /** maps over all arguments, collecting the contexts along the way */
  def checkDynamicBooleans(gc: GlobalContext, bs: List[Expression])(implicit alsoCheck: Boolean): (List[Expression], LocalContext) = {
    var lc = LocalContext.empty
    val bsC = bs.map { b =>
      val (bC, bB) = checkDynamicBoolean(gc.append(lc), b)
      lc = lc.append(bB)
      bC
    }
    (bsC, lc)
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

  /** checks if a pattern can be assigned to, returns the list of assigned-to atoms */
  private def checkAssignable(gc: GlobalContext, target: Expression): List[Expression] = {
    def check(t: Expression) = checkAssignable(gc, t)
    implicit val cause = target
    target match {
      case VarRef("") => Nil // anonyomous variable
      case VarRef(n) =>
        val vd = gc.local.lookup(n)
        if (!vd.mutable) fail("variable not mutable")
        List(target)
      case vd: VarDecl =>
        if (vd.defined) fail("defined variable not assignable")
        List(vd)
      case ClosedRef(n) => gc.lookupRegional(n) match {
        case Some(ed: ExprDecl) =>
          if (!ed.mutable) fail("assignment to immutable field")
          List(target)
        case _ => fail("not an assignable field")
      }
      case Tuple(es) => es flatMap check
      case CollectionValue(es,k) if !k.comm && !k.norep =>
        es flatMap check
      case OwnedExpr(o,d,e) =>
        o match {
          case _: Ref | _: VarRef =>
            checkAssignable(gc.push(d,Some(o)),e).map(OwnedExpr(o,d,_))
          case _ => fail("owner in pattern must be atomic")
        }
      case eo: ExprOver =>
        var res: List[Expression] = Nil
        EvalTraverser(eo) {e => res = res ::: check(e); e}
        res
      case Application(OpenRef(r),es) =>
        gc.lookupGlobal(r) match {
          case Some(ed: ExprDecl) if ed.dfO.isEmpty =>
          case _ => fail("function application not assignable")
        }
        es flatMap check
      case Application(BaseOperator(o,_),es) =>
        if (!o.invertible) fail("operator not invertible")
        es flatMap check
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
            case o: OwnedTheory => throw IError("impossible case") // could have some quote-like semantics
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
    // better take union than fail because of operations on collections
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
      case (_:ClosedRef | _:OpenRef | _: BaseType | ExceptionType | _: ClassType | _: ExprsOver, _) if aK == bK =>
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

object Checker {
  // This does not really belong here. But it feels too semantic to be part of GlobalContext
  /**
    * normalizes a well-formed theory expression into a TheoryValue
    * expands definitions and applied owners, but does not necessarily flatten TheoryValues
    * Examples: Assume gc + (o2:d2) + (o1:d1) |- r ---> {ds}
    * - then  gc |- o2.(o1.r) is (o2:d2).((o1:d1).r)
    *   and flattens to {ds} with . for ., o1 for .., o2 for ..., .. for ...., and so on
    * - then  gc |- (o2.o1).r is (o:d).r with o = (o2:d2).o1 and d = (o2:d2).d1
    *   thus  gc + (o:d) |- r ---> o2.{ds}
    *   and the expression flattens to the same result as before
    */
  def evaluateTheory(gc: GlobalContext, thy: Theory): TheoryValue = {
    // invariants: gcI |- thyI : THEORY,  gcI = gc.push(_)....push(_)
    var gcI = gc
    var thyI = thy
    while (true) {
      thy match {
        case OwnedTheory(o,d,t) =>
          gcI = gcI.push(d,Some(o))
          thyI = t
        case r: Ref =>
          val df = gcI.lookupModule(r).df
          val dfS = OwnersSubstitutor.applyTheory(gcI, df, gcI.regions.length - gc.regions.length)
          return evaluateTheory(gcI, dfS)
        case TheoryAsValue(t) =>
          // special case to undo any call of .toValue on one of the above
          return evaluateTheory(gcI, t)
        case tv: TheoryValue =>
          val tvO = OwnersSubstitutor.applyTheory(gcI, tv, gcI.regions.length - gc.regions.length)
          return tvO.toValue
      }
    }
    throw IError("impossible case")
  }
}

// TODO: magic functions for operator applications

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
  /** this when StringType expected */
  object asstring extends MagicFunction("toString")
  /** this[x] */
  object listElement extends MagicFunction("elemAt")
  /** x in this */
  object iteration extends MagicFunction("elements")
  /** this(args) */
  object application extends MagicFunction("apply")
  /** this.n */
  class projection(n: Int) extends MagicFunction("component_"+n)
  /** `this` */
  object evaluation extends MagicFunction("eval")
}
object MagicFunctions {
  val asType = "univ"
  /** this when Type expected */
  def typeOf(e: Expression, dom: Theory) = OwnedType(e,dom, ClosedRef(asType))
}

/*
/** a monad for tracking a [LocalContext] in addition to a value */
case class WithBinding[A](result: A, binding: LocalContext) {
  /** maps a function over the current value */
  def map[B](f: A => B) = WithBinding(f(result), binding)
  /** appends the bindings of the map-function to the current bindings */
  def flatMap[B](f: A => WithBinding[B]) = {
    val fr = f(result)
    WithBinding(fr.result, binding.append(fr.binding))
  }
  def get(warn: Boolean): A = {
    if (!binding.empty) throw PError("")
    result
  }
}
object WithBinding {
  /** injection into the monad */
  def apply[A](a: A) = WithBinding(a, LocalContext.empty)
}

/** statefully tracks bindings that arise during a computation, see [WithBinding] */
class BindingCollector(gcInit: GlobalContext) {
  private var gc = gcInit
  def append(lc: LocalContext): Unit = {
    gc = gc.append(lc)
  }
  /** applies a computation to the bindings collected so far and appends the bindings collected during it */
  def collect[A](f: GlobalContext => WithBinding[A]) = {
    val a = f(gc)
    append(a.binding)
    a.result
  }
  def extract = gc
}
object BindingCollector {
  /** the entry point for collecting bindings
   *
   * toplevel initialization: apply(gc,rec) {bc => f(bc)}
   * collecting inside f: wb.collect(bc) for any wb:WithBinding
   * extraction at the end: .result and .binding
   */
  def apply[A](gc: GlobalContext, recover: A)(f: BindingCollector => WithBinding[A]) = {
    val bc = new BindingCollector(gc)
    val res = recoverWith(recover) {
      f(bc)
    }
    WithBinding(r, bc.extract)
  }
}
*/