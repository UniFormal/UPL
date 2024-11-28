package info.kwarc.p

import SyntaxFragment.matchC

object Checker {
  private val debug = true

  case class Error(cause: SyntaxFragment,msg: String) extends PError(cause.loc + ": " + msg + " while checking " + cause.toString)
  def fail(m: String)(implicit cause: SyntaxFragment) =
    throw Error(cause,m)

  def checkProgram(p: Program): Program = matchC(p) {
    case Program(voc,mn) =>
      val gc = GlobalContext("")
      voc.foreach {d => d.global = true}
      val vocC = checkDeclarationsAndFlatten(gc, voc, true)
      val gcC = GlobalContext(Module.anonymous(vocC))
      val mnC = checkExpression(gcC,mn,AnyType)
      Program(vocC, mnC)
  }

  def checkDeclaration(gc: GlobalContext, decl: Declaration): Declaration = {
    if (debug) println("checking: " + decl)
    implicit val cause = decl
    val declC = decl match {
      case m:Module =>
        // checking will try to merge declarations of the same name, so no uniqueness check needed
        val envM = gc.add(m.copy(decls = Nil).copyFrom(m)).enter(m.name)
        if (!m.closed) {
          m.decls.foreach {_.global = true}
        }
        val declsC = checkDeclarationsAndFlatten(envM, m.decls, true)
        // check if this module has definitions for every abstract declaration in a realized theory
        val defines = declsC.collect {
          case sd: SymbolDeclaration if sd.dfO.isDefined => sd.name
        }
        declsC.foreach {
          case id: Include if id.realize => gc.voc.lookupModule(id.dom).get.undefined.foreach {sd =>
            if (!defines.contains(sd.name))
              fail("missing definition of " + id.dom/sd.name)
          }
          case _ =>
        }
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
            val (dfC,dfI) = inferExpression(gc,df)
            PurityChecker(dfC)(gc,())
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
    declC
  }

  private case class FlattenInput(decls: List[Declaration], alsoCheck: Boolean, alsoTranslate: Option[Expression]) {
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
  private def checkDeclarationsAndFlatten(gc: GlobalContext, decls: List[Declaration], keepFull: Boolean): List[Declaration] = {
    /* a FIFO queue of lists of declarations that must be flattened
     * Later on included lists of declarations will be prefixed with that flag negated and the definiens of the include.
     * It would be equivalent to keep a List[Declaration] instead of what is essentially a list of lists of declarations
     * if the former always holds the concatenation of the latter.
     * But our implementation is more efficient because it avoids that copying lists.
     */
    // initially, we need to flatten the original list, which must be checked but not translated
    var todo = List(FlattenInput(decls,true,None))
    var gcC = gc // will change as we process declarations
    // adds a declaration to the result, possibly merging with an existing one
    // returns true if added (redundant otherwise)
    def add(d: Declaration, current: FlattenInput): Boolean = {
      val dT = current.alsoTranslate match {
        case None => d
        case Some(o) => OwnerSubstitutor(o, d)
      }
      val old = gcC
      val existing = gcC.parentDecl.decls.view.map {e =>
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
            fail("declaration clash")(d)
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
        case Include(p, dfO, _) =>
          val m: Module = gc.voc.lookupModule(p).get
          todo ::= FlattenInput(m.decls, false, dfO)
        case _ =>
      }
    }
    // reverse 'done' while skipping redundant declarations
    var result: List[Declaration] = Nil
    gcC.parentDecl.decls.foreach {d =>
      if (!d.subsumed && (keepFull || d.subsuming || d.isInstanceOf[Include])) {
        result ::= d
      }
      // reset flags to avoid messing up the state in included modules
      d.subsumed = false
      d.subsuming = false
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
        if (abs.kind != sd.kind) fail("name is inherited but has kind " + abs.kind)
        // Concrete: error
        if (abs.dfO.isDefined) fail("name is inherited and already defined")
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
            val dfC = sd.dfO.map {df => checkExpression(gc,df,tpC, returnToHere = true)}
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
            val dfC = sd.dfO map {d =>
              checkExpression(gc,d,tpC, returnToHere = true)
            }
            sd.copy(tp = tpC,dfO = dfC)
        }
    }
  }

  def checkRegional(gc: GlobalContext, rc: RegionalContext): RegionalContext = {
    if (rc.theory == null && rc.owner.isEmpty) fail("underspecified region")(rc)
    val (thyC,ownC) = if (rc.theory == null) {
      val (oC,oI) = inferExpressionNorm(gc, rc.owner.get)
      oI match {
        case ClassType(t) => (t, Some(oC))
        case _ => fail("owner must be instance")(rc)
      }
    } else {
      val tC = checkTheory(gc,rc.theory)(rc.theory)
      val oC = rc.owner map {o =>
        checkExpression(gc,o,ClassType(tC))
      }
      (tC,oC)
    }
    val ctxC = checkLocal(gc.push(RegionalContext(thyC,ownC)), rc.local, false, false)
    RegionalContext(thyC,ownC,ctxC)
  }
  def checkTheoryPath(gc: GlobalContext, p: Path)(implicit cause: SyntaxFragment) = {
    gc.resolvePath(p) match {
      case Some((pC, m: Module)) => pC
      case _ => fail("not a module")
    }
  }

  // TODO totality check of realize
  def checkTheory(gc: GlobalContext, thy: Theory)(implicit cause: SyntaxFragment): Theory = {
    if (thy.isFlat) return thy
    val mod = thy.toModule
    val gcI = gc.add(mod.copy(decls = Nil)).enter(mod.name)
    val declsC = checkDeclarationsAndFlatten(gcI,thy.decls,false)
    // remove realize flags, which are irrelevant from the outside
    val declsCN = declsC map {
      case id : Include if id.realize => id.copy(realize = false)
      case d => d
    }
    val t = Theory(declsCN)
    t.isFlat = true
    t
  }
  def checkLocal(gc: GlobalContext,c: LocalContext,allowDefinitions: Boolean,allowMutable: Boolean): LocalContext = {
    var gcL = gc
    val declsC = c.decls.map {vd =>
      val vdC = checkVarDecl(gcL,vd,allowDefinitions,allowMutable)
      gcL = gcL.append(vdC)
      vdC
    }
    LocalContext(declsC)
  }

  def checkVarDecl(gc: GlobalContext,vd: VarDecl,allowDefinitions: Boolean,allowMutable: Boolean): VarDecl = {
    implicit val cause = vd
    if (vd.mutable && !allowMutable) fail("mutable variable not allowed here")
    if (vd.defined && !allowDefinitions) fail("defined variable not allowed here")
    val tpC = checkType(gc,vd.tp)
    val dfC = vd.dfO map {d => checkExpression(gc,d,tpC, returnToHere = true)}
    VarDecl(vd.name,tpC.skipUnknown,dfC,vd.mutable)
  }

  /** theory a subsumbed by b */
  def isSubtheory(a: Theory, b: Theory) = {
    a.decls.forall(p => b.decls.contains(p))
  }
  /** context a subsumed by b */
  def isSubcontext(a: LocalContext, b: LocalContext) = {
    a.decls.forall(d => b.decls.contains(d))
  }
  /** environment a subsumed by b */
  def isSubregion(a: RegionalContext, b: RegionalContext) = {
    isSubtheory(a.theory, b.theory) && isSubcontext(a.local,b.local)
  }

  // ***************** Types **************************************
  def checkType(gc: GlobalContext,tp: Type, bound: Type): Type = {
    val tpC = checkType(gc,tp)
    checkSubtype(gc, tpC, bound)(tp)
    tpC
  }
  def checkType(gc: GlobalContext, tpA: Type): Type = {
    implicit val cause = tpA
    def r(x:Type): Type = checkType(gc,x)
    disambiguateOwnedObject(gc, tpA).foreach {corrected => return checkType(gc, corrected)}
    // tp != tA only if tpA is an unresolved reference
    val (tpR, sdCached) = gc.resolveName(tpA).getOrElse(fail("unknown identifier"))
    val tp = tpR match {
      case t: Type => t
      case _ => fail("not a type")
    }
    matchC(tp) {
      case r: OpenRef =>
        val (rC,rd) = sdCached match {
          case Some(d) => (r, d)
          case _ => checkOpenRef(gc,r)
        }
        rd match {
          case td: TypeDecl => tp
          case m: Module =>
            // indeterminate use of module as type interpreted as class type
            if (!m.closed) fail("open module not a type")
            ClassType(PhysicalTheory(rC.path))
          case _ => fail(s"$r is not a type")
        }
      case ClosedRef(n) =>
        sdCached match {
          case Some(_: TypeDecl) => tp
          case _ => fail("not a type")
        }
      case OwnedType(owner, tp) =>
        val (ownerC, ownerI) = inferExpressionNorm(gc, owner)
        PurityChecker(ownerC)(gc,())
        ownerI match {
          case ClassType(d) =>
            val envO = gc.push(d,Some(ownerC))
            val tpC = checkType(envO, tp)
            OwnedType(ownerC, tpC)
          case _ => fail("owner must be an instance")
        }
      case _: BaseType => tp
      case IntervalType(l, u) =>
        val lC = l map {e => checkExpressionPure(gc, e, IntType)}
        val uC = l map {e => checkExpressionPure(gc, e, IntType)}
        IntervalType(lC,uC)
      case CollectionType(a,k) => CollectionType(r(a),k)
      case ProdType(as) => ProdType(checkLocal(gc, as))
      case FunType(as,b) =>
        val asC = checkLocal(gc, as)
        val bC = checkType(gc.append(asC), b)
        FunType(asC, bC)
      case ClassType(thy) =>
        val thyC = checkTheory(gc, thy)(tp)
        ClassType(thyC)
      case ExprsOver(sc, q) =>
        val scC = checkTheory(gc, sc)
        val qC = checkType(gc.push(scC), q)
        ExprsOver(scC, qC)
      case ProofType(f) =>
        val fC = checkExpressionPure(gc, f, BoolType)
        ProofType(fC)
      case u: UnknownType =>
        if (u.known)
          checkType(gc, u.tp)
        else
          u // must be infered from later declarations
    }
  }

  /** a <: b */
  def checkSubtype(gc: GlobalContext, a: Type, b: Type)(implicit cause: SyntaxFragment): Unit = {
    val equated = equateTypes(a,b)(true)
    if (equated) return
    (a,b) match {
      case (_,AnyType) => AnyType
      case (EmptyType,_) =>
      case (_:IntervalType,(IntType|RatType)) =>
      case (IntType,RatType) =>
      case (a: IntervalType, b: IntervalType) =>
        (a.lower,b.lower) match {
          case (_,None) =>
          case (None,Some(_)) => fail("interval is not subtype")
          case (Some(i),Some(j)) =>
            val c = simplifyExpression(gc,GreaterEq(i,j))
            if (c == BoolValue(true)) {}
            else if (c == BoolValue(false)) fail("interval is not subtype")
            else {} // type-checking incomplete}
        }
        (a.upper,b.upper) match {
          case (_, None) =>
          case (None, Some(_)) => fail("interval is not subtype")
          case (Some(i), Some(j)) =>
            val c = simplifyExpression(gc, LessEq(i,j))
            if (c == BoolValue(true)) {}
            else if (c == BoolValue(false)) fail("interval is not subtype")
            else {}// type-checking incomplete}
        }
      case (CollectionType(a,k),CollectionType(b,l)) =>
        if (!(k sub l)) fail(s"collection type $k is not subtype of collection type $l")
        checkSubtype(gc,a,b)
      case (ProdType(as),ProdType(bs)) =>
        checkSubcontext(gc, as, bs)
      case (FunType(as,o),FunType(bs,p)) =>
        checkSubcontext(gc, bs, as)
        checkSubtype(gc.append(bs),o,b)
      case (ExprsOver(aT,u),ExprsOver(bT,v)) =>
        if (!isSubtheory(aT,bT)) fail("not quoted from the same theory")
        checkSubtype(gc.push(aT),u,v)
      case (ClassType(aT),ClassType(bT)) =>
        // model of aT or model of bT, i.e., model of intersection
        if (!isSubtheory(bT,aT)) // larger theory = smaller type
          fail("subtype must be larger theory")
      case _ =>
        val aN = typeNormalize(gc, a)
        val bN = typeNormalize(gc, b)
        if (a != aN || b != bN)
          checkSubtype(gc,aN,bN)
        else
          fail(s"found: $a; expected: $b")
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
    val equated = equateTypes(a,b)(true)
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
        val abs = (as zip bs).map {case (x,y) => typeUnion(gc,x,y)}
        ProdType(abs)
      case (FunType(as,o),FunType(bs,p)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeIntersection(gc,x,y)}
        val op = typeUnion(gc,o,p)
        FunType(abs,op)
      case (ExprsOver(aT,u), ExprsOver(bT, v)) =>
        if (aT != bT) fail("not quoted from the same theory")
        val thyU = theoryUnion(gc, aT, bT)
        // aT-expression of type u or bT-expression of type v, i.e., expression over union of union type
        ExprsOver(thyU, typeUnion(gc.push(thyU), u, v))
      case (ClassType(aT), ClassType(bT)) =>
        // model of aT or model of bT, i.e., model of intersection
        val i = theoryIntersection(gc,aT,bT)
        if (i.decls.isEmpty) AnyType else ClassType(i)
      case _ =>
        val aN = typeNormalize(gc, a)
        val bN = typeNormalize(gc, b)
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
     val equated = equateTypes(a,b)(true)
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
        val abs = (as zip bs).map {case (x,y) => typeIntersection(gc,x,y)}
        ProdType(abs)
      case (FunType(as,o),FunType(bs,p)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeUnion(gc,x,y)}
        val op = typeIntersection(gc,o,p)
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
        val aN = typeNormalize(gc, a)
        val bN = typeNormalize(gc, b)
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
  def typeNormalize(gc: GlobalContext, tp: Type): Type = {
    implicit val cause = tp
    def n(t: Type) = typeNormalize(gc, t)
    def f(t: Theory) = checkTheory(gc, t)
    matchC(tp) {
      case ClosedRef(f) => gc.lookupRegional(f) match {
        case Some(td: TypeDecl) => td.dfO match {
          case Some(df) => n(df)
          case None => tp
        }
        case _ => fail("illegal type")(tp) // impossible if tp is checked
      }
      case OpenRef(p) =>
        gc.voc.lookupPath(p) match {
          case Some(td: TypeDecl) => td.dfO match {
            case None => tp
            case Some(df) => n(df)
          }
          case _ => fail("illegal type")(tp) // impossible if tp is checked
        }
      case OwnedType(own, t) =>
        val tpS = OwnerSubstitutor(own, t)
        if (tpS != tp) typeNormalize(gc, tpS) else tpS
      case _: BaseType => tp
      case IntervalType(l,u) =>
        val lS = l map {e => simplifyExpression(gc, e)}
        val uS = u map {e => simplifyExpression(gc, e)}
        (lS,uS) match {
          case (Some(IntValue(l)), Some(IntValue(u))) if l > u => EmptyType
          case (None,None) => IntType
          case _ => IntervalType(lS,uS)
        }
      case FunType(as,a) => FunType(as map n, n(a))
      case ProdType(as) => ProdType(as map n)
      case CollectionType(a,k) => CollectionType(n(a), k)
      case ClassType(sc) => ClassType(f(sc))
      case ExprsOver(sc, t) =>
        val thyN = f(sc)
        ExprsOver(thyN, n(t))
      case _:ProofType => tp
      case u: UnknownType => if (u.known) n(u.tp) else u
    }
  }

  // ***************** Expressions **************************************
  /** checks an expression against an expected type
    *
    * This is helpful for infering omitted information in introduction forms from their expected type.
    * In most cases, this defers to type inference and subtype checking.
    */
  def checkExpression(gc: GlobalContext,exp: Expression,tp: Type, returnToHere: Boolean = false): Expression = {
    implicit val cause = exp
    def withReturnVar(q: GlobalContext, o: Type) = if (returnToHere) q.append(VarDecl.output(o)) else q
    disambiguateOwnedObject(gc, exp).foreach {corrected => return checkExpression(gc, corrected, tp)}
    val tpN = typeNormalize(gc, tp)
    val eC = (exp,tpN) match {
      case (i, IntervalType(l,u)) =>
        val (iC,iI) = inferExpression(gc,i)
        iI match {
          case IntType =>
            // inference of values return Int, so we need to see if we can downcast
            val lCond = l map {b => LessEq(b,i)} getOrElse BoolValue(true)
            val uCond = u map {b => LessEq(i,b)} getOrElse BoolValue(true)
            simplifyExpression(gc, And(lCond,uCond)) match {
              case BoolValue(true) =>
              case BoolValue(false) => fail("out of interval")
              case _ => fail("cannot determine interval mebmership")// incomplete
            }
          case _ =>
            checkSubtype(gc,iI,tpN)
        }
        iC
      case (CollectionValue(es), CollectionType(t,kind)) =>
        if (kind.sizeOne && es.length > 1) fail("option type must have at most one element")
        val esC = es.map(e => checkExpression(gc,e,t))
        CollectionValue(esC)
      case (Tuple(es),ProdType(ts)) =>
        if (es.length != ts.length) fail("wrong number of components in tuple")
        val esC = (es zip ts) map {case (e,t) => checkExpression(gc,e,t)}
        Tuple(esC)
      case (Lambda(ins,bd), ft) =>
        // this handles arbitrary function types so that we can always insert the return variable if necessary
        val insC = checkLocal(gc,ins,false,false)
        val outType = ft match {
          case FunType(insE,outE) =>
            if (insC.decls.length != insE.length) fail("wrong number of variables in lambda")
            (insC.decls zip insE).foreach {case (inC,inE) =>
              checkSubtype(gc, inE, inC.tp)
            }
            outE
          case _ =>
            val inTypes = insC.decls.map(_.tp)
            val o = Type.unknown
            checkSubtype(gc, FunType(inTypes,o), ft)
            o
        }
        val gcB = withReturnVar(gc.append(insC), outType)
        val bdC = checkExpression(gcB,bd,outType)
        Lambda(insC,bdC)
      case (OwnedExpr(oe, e), OwnedType(ot, tp)) if oe == ot =>
        val (oC,oI) = inferExpression(gc, oe)
        oI match {
          case ClassType(d) =>
            val eC = checkExpression(gc.push(d,Some(oC)), e, tp)
            OwnedExpr(oC, eC)
          case _ => fail("owner must be class type")
        }
      case (Instance(thyA), ClassType(thyB)) =>
        val instC = checkTheory(gc, thyB union thyA)
        Instance(thyA)
      case (ExprOver(scE,e), ExprsOver(scT, tp)) =>
        val scTC = checkTheory(gc, scT)
        if (scE != null) {
          if (!isSubtheory(scE, scTC)) fail("quoted scope not part of expected type")
        }
        val eC = checkExpression(gc.push(scTC), e, tp)
        ExprOver(scTC, eC)
      case (Application(op: BaseOperator,args),_) if !op.tp.known =>
        val (argsC,argsI) = args.map(a => inferExpression(gc,a)).unzip
        val opTp = FunType(argsI,tpN)
        val opC = checkExpression(gc,op,opTp)
        Application(opC,argsC)
      case (BaseOperator(op,opTp),FunType(ins,out)) =>
        opTp match {
          case u: UnknownType =>
            val outI = inferOperator(gc,op,ins)
            checkSubtype(gc,outI,out)
            u.set(tpN)
          case _ =>
            checkSubtype(gc,opTp,tpN)
        }
        BaseOperator(op,tpN)
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
            val (eC,_) = inferExpression(gcL,e)
            // remember varibles for later expressions
            eC match {
              case vd: VarDecl =>
                val vdNoDef = if (vd.defined && vd.mutable) vd.copy(dfO = None) else vd
                gcL = gcL.append(vdNoDef)
              case _ =>
            }
            eC
          }
        }
        Block(esC)
      case _ =>
        val (eC,eI) = inferExpression(gc,exp)
        val mf = new MagicFunctions(gc)
        (tp,eI) match {
          case (StringType, mf.asstring(_,StringType)) =>
            mf.asstring.insert(eC,Nil)
          case (s:CollectionType, mf.iteration(_,t:CollectionType)) =>
            checkSubtype(gc,t,s)
            mf.iteration.insert(eC,Nil)
          case _ =>
            checkSubtype(gc,eI,tpN)
            eC
        }
    }
    eC.copyFrom(exp)
    eC
  }

  private def inferExpressionViaCheck(gc: GlobalContext, exp: Expression): (Expression,Type) = {
    val u = Type.unknown
    val eC = checkExpression(gc,exp, u)
    (eC, u.skipUnknown)
  }

  def checkExpressionPure(gc: GlobalContext, e: Expression, t: Type) = {
    val eC = checkExpression(gc, e, t)
    PurityChecker(e)(gc,())
    eC
  }

  /** like check, but also infers a context with the free variables */
  def checkExpressionPattern(gc: GlobalContext, e: Expression, tp: Type) = {
    val fvs = FreeVariables(gc,e)
    val fctx = LocalContext(fvs.map(n => VarDecl(n, Type.unknown)))
    val eC = checkExpression(gc.append(fctx), e, tp)
    val fctxI = fctx.decls.map {vd =>
      if (!vd.tp.known) fail("free variable whose type cannot be infered: " + vd.name)(e)
      vd.copy(tp = vd.tp.skipUnknown)
    }
    (LocalContext(fctxI), eC)
  }

  /** like [[inferExpression]] but with the type normalized */
  def inferExpressionNorm(gc: GlobalContext,e: Expression): (Expression,Type) = {
    val (eC,eI) = inferExpression(gc, e)
    (eC, typeNormalize(gc,eI))
  }

  /** checks an expression and infers its type
    *
    * This defers to [[checkExpression]] if it knows the expected type.
    */
  def inferExpression(gc: GlobalContext,expA: Expression): (Expression,Type) = {
    implicit val cause = expA
    val mf = new MagicFunctions(gc)
    // exp != expA only if exp is an unresolved reference
    val (expR, sdCached) = gc.resolveName(expA).getOrElse(fail("unknown identifier"))
    val exp = expR match {
      case e: Expression => e
      case _ => fail("not an expression")
    }
    disambiguateOwnedObject(gc, exp).foreach {corrected => return inferExpression(gc, corrected)}
    // check exp and infer its type
    val (expC,expI) = exp match {
      case e: BaseValue => (e,e.tp)
      case op: BaseOperator =>
        if (!op.tp.known) {
          fail("cannot infer type of operator")
        }
        val ft = typeNormalize(gc,op.tp) match {
          case ft: FunType => ft
          case _ => fail("operator type not a function")
        }
        val out = inferOperator(gc,op.operator,ft.ins)
        checkSubtype(gc,out,ft.out)(exp)
        (BaseOperator(op.operator,ft),op.tp)
      case r: OpenRef =>
        val (rC,rd) = sdCached match {
          case Some(d) => (r, d)
          case _ => checkOpenRef(gc,r)
        }
        rd match {
          case ed: ExprDecl =>
            (rC, ed.tp)
          case _ => fail(s"$r is not an expression")
        }
      case ClosedRef(n) =>
        sdCached match {
          case Some(ed: ExprDecl) => (exp, ed.tp)
          case _ => fail("not an expression")
        }
      case OwnedExpr(owner, e) =>
        val (ownerC, ownerI) = inferExpressionNorm(gc, owner)
        ownerI match {
          case ClassType(d) =>
            val envO = gc.push(d,Some(ownerC))
            val (eC, eI) = inferExpression(envO, e)
            (OwnedExpr(ownerC, eC), OwnedType(ownerC, eI))
          case _ => fail("owner must be an instance")
        }
      case VarRef(n) =>
        (exp,gc.local.lookup(n).tp)
      case Instance(thy) =>
        val thyR = thy match {
          case ExtendedTheory(p,ds) => Theory(Include(p,None,true)::ds)
          case _ => fail("instance must be of atomic theory")
        }
        // TODO: check that ds do not have side effects outside of itself
        val thyC = checkTheory(gc,thyR)
        (Instance(thyC),ClassType(thyC))
      case ExprOver(sc,q) =>
        val scC = checkTheory(gc,sc)
        val (qC,qI) = inferExpression(gc.push(scC),q)
        (ExprOver(scC,qC),ExprsOver(scC,qI))
      case Eval(e) =>
        if (gc.regions.isEmpty) fail("eval outside quotation")
        val (eC,eI) = inferExpressionNorm(gc.pop(),e)
        eI match {
          case ExprsOver(eT,q) =>
            if (!isSubtheory(eT, gc.theory)) fail("quoted over wrong theory")
            (Eval(eC),q)
          case mf.evaluation(_,a) =>
            (mf.evaluation.insert(eC, Nil), a)
          case _ => fail("not a quoted expression")
        }
      case MatchCase(ctx, p, b) =>
        fail("match case outside of match")
      case Lambda(ins,bd) =>
        val insC = checkLocal(gc,ins,false,false)
        val inTypes = insC.decls.map(_.tp)
        val (bdC,bdI) = inferExpression(gc.append(insC),bd)
        (Lambda(insC,bdC),FunType(inTypes,bdI))
      case Application(f,as) =>
        f match {
          case op: BaseOperator if !op.tp.known =>
            // for an operator of unknown type, we need to infer the argument types first
            val (asC,asI) = as.map(a => inferExpression(gc,a)).unzip
            val out = inferOperator(gc,op.operator,asI)
            val opC = op.copy(tp = FunType(asI,out))
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
              case u: UnknownType if !u.known =>
                val uis = as.map(_ => Type.unknown())
                val uo = Type.unknown()
                u.set(FunType(uis,uo))
                (fC,uis,uo)
              case mf.application(_,FunType(i,o)) => (mf.application.insert(fC,as),i,o)
              case _ => fail("not a function")(f)
            }
            if (as.length != ins.length) fail("wrong number of arguments")
            val asC = (as zip ins).map {case (a,i) => checkExpression(gc,a,i)}
            (Application(fM,asC),out)
        }
      case Tuple(es) =>
        val (esC,esI) = es.map(e => inferExpression(gc,e)).unzip
        (Tuple(esC),ProdType(esI))
      case Projection(tup, p) =>
        val mfp = new mf.projection(p)
        val (tupC,tupI) = inferExpressionNorm(gc,tup)
        tupI match {
          case ProdType(ts) =>
            if (p <= 0) fail("non-positive index")
            if (p > ts.length) fail("index out of bounds")
            (Projection(tupC,p), ts(p-1))
          case mfp(_,a) =>
            (mfp.insert(tupC, List(IntValue(p))), a)
          case _ => fail("not a tuple")
        }
      case CollectionValue(es) =>
        val (esC,esI) = es.map(e => inferExpression(gc,e)).unzip
        val eI = typeUnion(gc,esI)
        val kind = if (es.length <= 1) CollectionKind.Option else CollectionKind.List // smallest applicable subquotient of List
        (CollectionValue(esC),CollectionType(eI, kind))
      case ListElem(l, p) =>
        val u = Type.unknown
        val lC = checkExpression(gc, l, CollectionType(u, CollectionKind.UList))
        val pC = checkExpression(gc, p, IntType)
        // index bounds not checked
        (ListElem(lC,pC), u)
      case Quantifier(q,vars,bd) =>
        val varsC = checkLocal(gc, vars, false, false)
        val bdC = checkExpressionPure(gc.append(varsC), bd, BoolType)
        (Quantifier(q,varsC,bdC), BoolType)
      case Assert(f) =>
        val fC = checkExpressionPure(gc, f, BoolType)
        (Assert(fC), UnitType)
      case Block(es) =>
        inferExpressionViaCheck(gc, exp)
      case VarDecl(n, tp, vlO, mut, _) =>
        val (tpC,vlC) = if (!tp.known) {
          vlO match {
            case None => fail("untyped variables")
            case Some(vl) =>
              val (vlC,vlI) = inferExpression(gc, vl)
              (vlI, Some(vlC))
          }
        } else {
          val tpC = checkType(gc, tp)
          val vlC = vlO map {vl => checkExpression(gc,vl,tp)}
          (tpC,vlC)
        }
        (VarDecl(n,tpC,vlC,mut),UnitType)
      case Assign(e,df) =>
        val (eC,eI) = inferExpression(gc, e)
        val dfC = checkExpression(gc,df,eI)
        checkAssignable(gc,e)
        (Assign(eC,dfC),UnitType)
      case While(cond,bd) =>
        val condC = checkExpression(gc, cond, BoolType)
        val bdC = checkExpression(gc, bd, AnyType)
        (While(condC, bdC), UnitType)
      case IfThenElse(cond,thn, elsO) =>
        val condC = checkExpression(gc, cond, BoolType)
        val (thnC,thnI) = inferExpressionNorm(gc, thn)
        val (elsOC, eI) = elsO match {
          case Some(els) =>
            val (elsC, elsI) = inferExpressionNorm(gc, els)
            val u = typeUnion(gc, thnI, elsI)
            if (u == AnyType) fail(s"branches have incompatible types: $thnI vs. $elsI")
            (Some(elsC), u)
          case None => (None,UnitType)
        }
        (IfThenElse(condC, thnC, elsOC), eI)
      case Match(e,cs,h) =>
        val (eC,eI) = inferExpression(gc,e)
        val (patType,bodyType) = if (h) {
          (AnyType,Some(eI))
        } else {
          (eI,None)
        }
        val (csC,csI) = cs.map {case MatchCase(ctx,p,b) =>
          val (ctxC,pC) = if (ctx == null) {
            checkExpressionPattern(gc,p,patType)
          } else {
            val cC = checkLocal(gc, ctx, false, false)
            (cC, checkExpression(gc.append(cC), p, patType))
          }
          val (bC,bI) = bodyType match {
            case None => inferExpression(gc.append(ctxC),b)
            case Some(bt) => (checkExpression(gc.append(ctxC),b,bt), bt)
          }
          (MatchCase(ctxC,pC,bC),bI)
        }.unzip
        val mI = if (h) eI else typeUnion(gc,csI)
        if (mI == AnyType) fail(s"branches have incompatible types: " + csI.mkString(", "))
        (Match(eC,csC,h),mI)
      case For(vd, range, bd) =>
        val vdC = checkVarDecl(gc,vd,false,false)
        val rangeC = checkExpression(gc, range, CollectionKind.UList(vdC.tp))
        val (bdC,bdI) = inferExpression(gc.append(vdC), bd)
        (For(vdC, rangeC, bdC), CollectionKind.List(bdI)) // map may introduce repetitions
      case Return(e,thrw) =>
        val rt = if (thrw) AnyType else gc.getOutput.getOrElse(fail("return not allowed here"))
        val eC = checkExpression(gc,e,rt)
        (Return(eC,thrw), EmptyType)
    }
    expC.copyFrom(exp)
    (expC,expI)
  }

  private object PurityChecker extends StatelessTraverser {
    override def apply(e: Expression)(implicit gc: GlobalContext,a:Unit) = {
      e match {
        case OpenRef(p) => gc.voc.lookupPath(p) match {
          case Some(ed: ExprDecl) => if (ed.mutable) fail("state-dependent")
          case _ =>
        }
        case ClosedRef(n) => gc.lookupRegional(n) match {
          case Some(ed: ExprDecl) => if  (ed.mutable) fail("state-dependent")
          case _ =>
        }
        case VarRef(n) => if (gc.lookup(n).mutable) fail("state-dependent")
        case _: Instance => fail("state-dependent")
        case _: Assign => fail("state-changing")
        case _: While => fail("potentially non-terminating")
        case _: Return => fail("potentially non-value")
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
      case ClosedRef(n) => gc.lookupRegional(n) match {
        case Some(ed: ExprDecl) =>
          if (!ed.mutable) fail("assignment to immutable field")
        case _ => fail("not an assignable field")
      }
      case Tuple(es) => es foreach check
      case CollectionValue(es) => es foreach check // TODO depends on kind
      case eo: ExprOver => EvalTraverser(eo) {e => check(e); e}
      case Application(OpenRef(r),es) =>
        gc.voc.lookupPath(r) match {
          case Some(ed: ExprDecl) if ed.dfO.isEmpty =>
          case _ => fail("function application not assignable")
        }
        es foreach check
      case _ => fail("expression not assignable")
    }
  }

  def simplifyExpression(gc: GlobalContext, exp: Expression) = Simplify(exp)(gc,())

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
    * because the parser cannot disambiguate these */
  // the type bound allows taking a Type or an Expression and returning the same
  private def disambiguateOwnedObject[A >: Type with Expression](gc: GlobalContext, o: A): Option[A] = o match {
    case o: OwnedObject =>
      val ownerInfo = o.owner match {
        case OpenRef(p) => gc.resolvePath(p) flatMap {
          case (pR, m: Module) => Some((pR, m.closed))
          case _ => None
        }
        case ClosedRef(n) => gc.resolveName(o.owner) flatMap {
          case (_:ClosedRef,Some(m:Module)) => Some((Path(n), m.closed))
          case (OpenRef(pR), _) => Some((pR,false))
          case _ => None
        }
        case _ => None
      }
      ownerInfo map {case (p,closed) =>
        if (closed) {
          val sc = PhysicalTheory(p)
          o match {
            case o: OwnedType => ExprsOver(sc,o.owned).copyFrom(o).asInstanceOf[A] // guaranteed to work, but needed by Scala compiler
            case o: OwnedExpr => ExprOver(sc,o.owned).copyFrom(o).asInstanceOf[A]
          }
        } else {
          o.owned match {
            case ClosedRef(n) => OpenRef(p/n)
            case _ => fail("open module cannot own expressions")(o)
          }
        }
      }
    case _ => None
  }

  def inferOperator(gc: GlobalContext,op: Operator,ins: List[Type])(implicit cause: Expression): Type = {
    val param = Type.unknown()
    val possibleTypes = op.types:::op.polyTypes(param)
    val matchResults = possibleTypes.map {case f@FunType(expected,_) =>
      matchTypes(ProdType(ins), ProdType(expected))(true).map((f,_))
    }
    val matchingTypes = matchResults.flatMap(_.toList)
    if (matchingTypes.length == 0)
      fail("ill-typed operator")
    val outs = matchingTypes.map(_._1.out).distinct
    // infer return type if all possible types agree
    val out = if (outs.length == 1) outs.head else
      fail("cannot disambiguate operator")
    // find all unknowns that all possible types agree on
    var commonAssignments: TypeAssignments = matchingTypes.head._2
    matchingTypes.tail.foreach {case (_,next) => commonAssignments = commonAssignments intersect next}
    // if we found multiple assignments for the parameter of this operator, take their union
    val (paramAssignments, otherAssignments) = commonAssignments.partition(_._1 == param)
    val paramAssignment = if (paramAssignments.isEmpty) Nil
       else List((param, typeUnion(gc, paramAssignments.map(_._2))))
    // better take union than fail because of equality and operations on collections
    assignAsMatched(paramAssignment:::otherAssignments)
    out
  }

  private type TypeAssignments = List[(UnknownType,Type)]
  /** checks if the types can be made equal by assigning to unknowns, returns those assignments */
  private def matchTypes(a: Type, b: Type)(implicit allowSubtyping: Boolean): Option[TypeAssignments] = (a.skipUnknown,b.skipUnknown) match {
    case (a,b) if a == b => Some(Nil)
    case (u: UnknownType, k) if !u.known => Some(List((u,k)))
    case (k, u: UnknownType) if k.known && !u.known => Some(List((u,k)))
    case (ProdType(as), ProdType(bs)) => matchTypeLists(as,bs)
    case (FunType(as,c), FunType(bs,d)) => matchTypeLists(c::bs,d::as)
    case (CollectionType(c,k), CollectionType(d,l)) =>
      if (k == l || (allowSubtyping && (k sub l)))
        matchTypes(c,d)
      else
        None
    case _ => None
  }
  private def matchTypeLists(as: List[Type], bs: List[Type])(implicit allowSubtyping: Boolean): Option[TypeAssignments] = {
    if (as.length != bs.length) return None
    val cs = (as zip bs).map{case (x,y) => matchTypes(x,y)}
    if (cs.forall(_.isDefined)) Some(cs.flatMap(_.get)) else None
  }
  /** applies assignments returned by matchTypes */
  private def assignAsMatched(as: TypeAssignments) = as.distinct.foreach {case (u,a) =>
    u.set(a)
  }
  /** like matchTypes, but makes the assignments right away if matching is possible */
  private def equateTypes(a: Type, b: Type)(allowSubtyping: Boolean) = matchTypes(a,b)(allowSubtyping) match {
    case Some(uas) => assignAsMatched(uas); true
    case None => false
  }
}

class MagicFunctions(gc: GlobalContext) {
  class MagicFunction(name: String) {
    def insert(owner: Expression,args: List[Expression]) = Application(owner.field(name),args)
    def unapply(tp: Type) = tp match {
      case ClassType(thy) => gc.push(thy,None).lookupRegional(name) match {
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