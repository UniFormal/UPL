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
      val vocC = checkDeclarationsAndFlatten(gc, p.voc)
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
        val envM = gc.add(m.copy(decls = Nil)).enter(m.name)
        val declsC = checkDeclarationsAndFlatten(envM, m.decls)
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
          val dfOC = id.dfO map {d => checkExpression(gc,d,ClassType(Theory(domC)))}
          Include(domC,dfOC,id.realize)
        } else id.dfO match {
          case None => fail("untyped include")
          case Some(df) =>
            // infer domain from definiens
            val (dfC,dfI) = inferExpression(gc,df)
            dfI match {
              case ClassType(Theory(List(p))) =>
                Include(p, Some(dfC), id.realize)
              case _ => fail("domain not an atomic theory")
            }
        }
        // TODO check purity of definiens
      case sd: SymbolDeclaration =>
        checkSymbolDeclaration(gc, gc.currentParent, sd)
        // TODO check purity of definiens
    }
    declC.copyFrom(decl)
    declC
  }

  private case class FlattenInput(decls: List[Declaration], alsoCheck: Boolean, alsoTranslate: Option[Expression]) {
    def tail = copy(decls = decls.tail)
  }
  /** checking and flattening a list of declarations
      - symbol declarations: keep, possibly merge/clash with existing declaration
      -include T [=m]: keep, possibly merge/clash,
        then also add body of T, recursively addpossibly changing all expressions e to m.e
        this causes an exponential blow-up, but that is acceptable because
        - unrefined declarations are not copied
        - refinements by defined includes need a shallow copy of the declaration
     Any two declarations for the same name get merged as follows:
     - A subsumed declarations is marked redundant and removed at the end.
     - If a new declaration has to be generated, it is added and both refinees are removed.
     - Declarations are marked to retain the original list.
    */

  private def checkDeclarationsAndFlatten(gc: GlobalContext, decls: List[Declaration]): List[Declaration] = {
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
          case Declaration.Identical | Declaration.Subsumes =>
            if (debug) println("subsumed declaration: " + dT)
          // new declaration is redundant: nothing to do
          case Declaration.SubsumedBy =>
            // old declaration is redundant: mark it for later removal
            e.redundant = true
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
      if (!d.redundant) {
        result ::= d
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
  private def checkSymbolDeclaration(gc: GlobalContext, parent: Path, sd: SymbolDeclaration): SymbolDeclaration = {
    implicit val cause = sd
    gc.voc.lookupPath(parent/sd.name) match {
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
            val dfC = sd.dfO.map {df => checkExpression(gc,df,tpC)}
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
              checkExpression(gc,d,tpC)
            }
            sd.copy(tp = tpC,dfO = dfC)
        }
    }
  }

  def checkRegional(gc: GlobalContext, rc: RegionalContext): RegionalContext = {
    val thyC = checkTheory(gc,rc.theory)(rc.theory)
    val ctxC = checkLocal(gc.push(thyC), rc.local, false, false)
    RegionalContext(thyC,ctxC)
  }
  def checkTheoryPath(gc: GlobalContext, p: Path)(implicit cause: SyntaxFragment) = {
    resolvePath(gc, p) match {
      case (pC, m: Module) => pC
      case _ => fail("not a module")
    }
  }
  def checkTheory(gc: GlobalContext, thy: Theory)(implicit cause: SyntaxFragment) = {
    val partsC = thy.parts.map {p => checkTheoryPath(gc,p)}
    val flat = partsC.flatMap {p => gc.voc.lookupModule(p).get.supers}.distinct
    // TODO: check compatibility of all parts with each other
    val thyC = Theory(flat)
    thy.isFlat = true
    thyC
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
    val dfC = vd.dfO map {d => checkExpression(gc,d,tpC)}
    VarDecl(vd.name,tpC.skipUnknown,dfC,vd.mutable)
  }

  /** theory a subsumbed by b */
  def isSubtheory(a: Theory, b: Theory) = {
    a.parts.forall(p => b.parts.contains(p))
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
    correctFreeOwner(gc, tpA).foreach {corrected => return checkType(gc, corrected)}
    // tp != tA only if tpA is an unresolved reference
    val (tpR, sdCached) = resolveName(gc, tpA)
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
            ClassType(Theory(rC.path))
          case _ => fail(s"$r is not a type")
        }
      case ClosedRef(n) =>
        sdCached match {
          case Some(_: TypeDecl) => tp
          case _ => fail("not a type")
        }
      case OwnedType(owner, tp) =>
        val (ownerC, ownerI) = inferExpression(gc, owner)
        ownerI match {
          case ClassType(d) =>
            val envO = gc.push(d)
            val tpC = checkType(envO, tp)
            OwnedType(ownerC, tpC)
          case _ => fail("owner must be an instance")
        }
      case _: BaseType => tp
      case tp: TypeOperator =>
        tp.children.foreach(c => checkType(gc,c))
        tp
      case ClassType(thy) =>
        val thyC = checkTheory(gc, thy)(tp)
        ClassType(thyC)
      case ExprsOver(re, q) =>
        val reC = checkRegional(gc, re)
        val qC = checkType(gc.push(reC), q)
        ExprsOver(reC, qC)
      case u: UnknownType =>
        if (u.known)
          checkType(gc, u.tp)
        else
          u // must be infered from later declarations
    }
  }

  /** a <: b */
  def checkSubtype(gc: GlobalContext, a: Type, b: Type)(implicit cause: SyntaxFragment): Unit = {
    val equated = equateTypes(a,b)
    if (equated) return
    (a,b) match {
      case (_,AnyType) => AnyType
      case (EmptyType,_) =>
      case (IntType,RatType) =>
      case (ListType(x),ListType(y)) => checkSubtype(gc,x,y)
      case (ProdType(as),ProdType(bs)) if as.length == bs.length =>
        (as zip bs).foreach {case (x,y) => checkSubtype(gc,x,y)}
      case (FunType(as,o),FunType(bs,p)) if as.length == bs.length =>
        (as zip bs).foreach {case (x,y) => checkSubtype(gc,y,x)}
        checkSubtype(gc,o,b)
      case (ExprsOver(aT,u),ExprsOver(bT,v)) =>
        if (!isSubregion(aT,bT)) fail("not quoted in the same context")
        checkSubtype(gc.push(aT),u,v)
      case (ClassType(aT),ClassType(bT)) =>
        // model of aT or model of bT, i.e., model of intersection
        if (!isSubtheory(bT,aT)) // larger theory = smaller type
          fail("subtype must be larger theory")
      case _ =>
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
    val equated = equateTypes(a,b)
    if (equated) return a
    // proper subtyping
    (a,b) match {
      case (AnyType,_) | (_,AnyType) => AnyType
      case (EmptyType,t) => t
      case (t,EmptyType) => t
      case (IntType,RatType) | (RatType,IntType) => RatType
      case (ListType(a),ListType(b)) => ListType(typeUnion(gc,a,b))
      case (ProdType(as),ProdType(bs)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeUnion(gc,x,y)}
        ProdType(abs)
      case (FunType(as,o),FunType(bs,p)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeIntersection(gc,x,y)}
        val op = typeUnion(gc,o,p)
        FunType(abs,op)
      case (ExprsOver(aT,u), ExprsOver(bT, v)) =>
        if (aT != bT) fail("not quoted in the same context")
        val thyU = theoryUnion(gc, aT.theory, bT.theory)
        val ctxU = (aT.local.decls ::: bT.local.decls).distinct
        val scopeU =  RegionalContext(thyU, LocalContext(ctxU))
        val varNames = ctxU.map(_.name)
        if (varNames.distinct != varNames) fail("incompatible variable names")
        // aT-expression of type u or bT-expression of type v, i.e., expression over union of union type
        ExprsOver(scopeU, typeUnion(gc.push(scopeU), u, v))
      case (ClassType(aT), ClassType(bT)) =>
        // model of aT or model of bT, i.e., model of intersection
        val i = theoryIntersection(gc,aT,bT)
        if (i.parts.isEmpty) AnyType else ClassType(i)
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
     val equated = equateTypes(a,b)
     if (equated) return a
    (a,b) match {
      case (AnyType,t) => t
      case (t,AnyType) => t
      case (EmptyType,_) | (_,EmptyType) => EmptyType
      case (IntType,RatType) | (RatType,IntType) => IntType
      case (ListType(a),ListType(b)) => ListType(typeIntersection(gc,a,b))
      case (ProdType(as),ProdType(bs)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeIntersection(gc,x,y)}
        ProdType(abs)
      case (FunType(as,o),FunType(bs,p)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeUnion(gc,x,y)}
        val op = typeIntersection(gc,o,p)
        FunType(abs,op)
      case (ExprsOver(aT,u), ExprsOver(bT, v)) =>
        // aT-expression of type u and bT-expression of type v, i.e., expression over the intersection of intersection type
        val thyI = theoryIntersection(gc, aT.theory, bT.theory)
        val ctxI = aT.local.decls intersect bT.local.decls // todo: not necessarily well-formed
        val scopeI =  RegionalContext(thyI, LocalContext(ctxI))
        ExprsOver(scopeI, typeIntersection(gc.push(scopeI), u, v)) // todo: u,v might use variables
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
    val pqs = (a.parts ::: b.parts).distinct //TODO error if not compatible
    val thy = Theory(pqs)
    thy.isFlat = a.isFlat && b.isFlat // flat if the inputs are
    thy
  }

  /** intersection of theories: the union of all common includes */
  def theoryIntersection(gc: GlobalContext, a: Theory, b: Theory): Theory = {
    val pqs = a.parts intersect b.parts // TODO remove definiens if not the same
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
      case ClosedRef(f) => lookupClosed(gc, f) match {
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
      case FunType(as,a) => FunType(as map n, n(a))
      case ProdType(as) => ProdType(as map n)
      case ListType(a) => ListType(n(a))
      case OptionType(a) => OptionType(n(a))
      case ClassType(sc) => ClassType(f(sc))
      case ExprsOver(sc, t) =>
        val thyN = f(sc.theory)
        ExprsOver( RegionalContext(thyN, sc.local), n(t))
      case u: UnknownType => if (u.known) n(u.tp) else u
    }
  }

  // ***************** Expressions **************************************
  /** checks an expression against an expected type
    *
    * This is helpful for infering omitted information in introduction forms from their expected type.
    * In most cases, this defers to type inference and subtype checking.
    */
  def checkExpression(gc: GlobalContext,exp: Expression,tp: Type): Expression = {
    implicit val cause = exp
    correctFreeOwner(gc, exp).foreach {corrected => return checkExpression(gc, corrected, tp)}
    correctFreeOwner(gc, tp).foreach {corrected => return checkExpression(gc, exp, corrected)}
    val tpN = typeNormalize(gc, tp)
    val eC = (exp,tpN) match {
      case (ListValue(es),ListType(t)) =>
        val esC = es.map(e => checkExpression(gc,e,t))
        ListValue(esC)
      case (Tuple(es),ProdType(ts)) =>
        if (es.length != ts.length) fail("wrong number of components in tuple")
        val esC = (es zip ts) map {case (e,t) => checkExpression(gc,e,t)}
        Tuple(esC)
      case (Lambda(insG,outG),FunType(insE,outE)) =>
        if (insG.decls.length != insE.length) fail("wrong number of variables in lambda")
        (insG.decls zip insE).foreach {case (inG,inE) =>
          inG.tp match {
            case u: UnknownType =>
              u.set(inE)
            case _ =>
              checkSubtype(gc, inE, inG.tp)
          }
        }
        val insC = checkLocal(gc,insG,false,false)
        val outC = checkExpression(gc.append(insC),outG,outE)
        Lambda(insC,outC)
      case (OwnedExpr(oe, e), OwnedType(ot, tp)) if oe == ot =>
        val (oC,oI) = inferExpression(gc, oe)
        oI match {
          case ClassType(d) =>
            val eC = checkExpression(gc.push(d), e, tp)
            OwnedExpr(oC, eC)
          case _ => fail("owner must be class type")
        }
      case (ExprOver(scE,e), ExprsOver(scT, tp)) =>
        val scTC = checkRegional(gc, scT)
        if (scE != null) {
          if (!isSubregion(scE, scTC)) fail("quoted scope not part of expected type")
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
      case _ =>
        val (eC,eI) = inferExpression(gc,exp)
        val equated = equateTypes(eI,tpN)
        if (!equated) {
          checkSubtype(gc,eI,tpN)
        }
        eC
    }
    eC.copyFrom(exp)
    eC
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
    val (expR, sdCached) = resolveName(gc, expA)
    val exp = expR match {
      case e: Expression => e
      case _ => fail("not an expression")
    }
    correctFreeOwner(gc, expA).foreach {corrected => return inferExpression(gc, corrected)}
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
        val (ownerC, ownerI) = inferExpression(gc, owner)
        ownerI match {
          case ClassType(d) =>
            val envO = gc.push(d)
            val (eC, eI) = inferExpression(envO, e)
            (OwnedExpr(ownerC, eC), OwnedType(ownerC, eI))
          case _ => fail("owner must be an instance")
        }
      case VarRef(n) =>
        (exp,gc.local.lookup(n).tp)

      case Instance(thy,ds) =>
        val (thyC, thyD) = resolvePath(gc, thy)
        val mod = thyD match {
          case m: Module => m
          case _ => fail("not a module")
        }
        if (!mod.closed) fail("instance must be of closed module")
        var definedNames: List[String] = Nil
        val dsC = ds map {
          case ad: AtomicDeclaration if ad.dfO.isEmpty =>
            fail("undefined declaration in instance")(ad)
          case sd: SymbolDeclaration =>
            definedNames ::= sd.name
            checkSymbolDeclaration(gc, thyC, sd)
          case i: Include =>
            fail("include unsupported")(i)
        }
        mod.undefined.foreach {sd =>
          if (!definedNames.contains(sd.name)) fail("instance must define " + sd.name)
        }
        (Instance(thyC,dsC),ClassType(Theory(thyC)))
      case ExprOver(rc,q) =>
        val rcC = checkRegional(gc,rc)
        val (qC,qI) = inferExpression(gc.push(rcC),q)
        (ExprOver(rcC,qC),ExprsOver(rcC,qI))
      case Eval(e) =>
        if (gc.regions.isEmpty) fail("eval outside quotation")
        val (eC,eI) = inferExpressionNorm(gc.pop(),e)
        eI match {
          case ExprsOver(eT,q) =>
            if (!isSubregion(eT, gc.currentRegion)) fail("quoted over wrong theory")
            (Eval(eC),q)
          case mf.evaluation(_,a) =>
            (mf.evaluation.insert(eC, Nil), a)
          case _ => fail("not a quoted expression")
        }
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
                    return inferExpression(gc, Projection(f,i).copyFrom(exp))
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
            (Projection(tupC,p), ts(p))
          case mfp(_,a) =>
            (mfp.insert(tupC, List(IntValue(p))), a)
          case _ => fail("not a tuple")
        }
      case ListValue(es) =>
        val (esC,esI) = es.map(e => inferExpression(gc,e)).unzip
        val eI = typeUnion(gc,esI)
        (ListValue(esC),ListType(eI))
      case ListElem(l, p) =>
        val (lC,lI) = inferExpressionNorm(gc, l)
        val pC = checkExpression(gc, p, IntType)
        lI match {
          case ListOrUnknownType(t) =>
            // list index bound unchecked
            (ListElem(lC,pC), t)
          case mf.listElement(_,FunType(List(IntType),a)) =>
            (mf.listElement.insert(lC, List(pC)), a)
          case _ => fail("not a list")
        }
      case OptionValue(e) =>
         if (e == null) (exp, OptionType(EmptyType))
         else {
           val (eC,eI) = inferExpression(gc, e)
           (OptionValue(eC), OptionType(eI))
         }
      case Block(es) =>
        var gcL = gc // local environment, includes variables seen in the block so far
        var eTp: Type = UnitType // type of the last seen expression in the block
        val esC = es.map {e =>
          val (eC,eI) = inferExpression(gcL, e)
          eTp = eI
          eC match {
            case vd:VarDecl =>
              val vdNoDef = if (vd.defined && vd.mutable) vd.copy(dfO = None) else vd
              gcL = gcL.append(vdNoDef)
            case _ =>
          }
          eC
        }
        (Block(esC), eTp)
      case VarDecl(n, tp, vlO, mut) =>
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
      case For(n, range, bd) =>
        val (rangeC,rangeI) = inferExpressionNorm(gc, range)
        val (rangeM, nTp) = rangeI match {
          case ListOrUnknownType(t) => (rangeC, t)
          case mf.iteration(_,ListType(t)) => (mf.iteration.insert(rangeC, Nil), t)
          case _ => fail("not iterable")
        }
        val bdC = checkExpression(gc.append(VarDecl(n,nTp)), bd, AnyType)
        (For(n, rangeM, bdC), UnitType)
    }
    expC.copyFrom(exp)
    (expC,expI)
  }

  private def checkAssignable(gc: GlobalContext, target: Expression): Unit = {
    def check(t: Expression) = checkAssignable(gc, t)
    implicit val cause = target
    target match {
      case VarRef("") => // anonyomous variable
      case VarRef(n) =>
        val vd = gc.local.lookup(n)
        if (!vd.mutable) fail("variable not mutable")
      case ClosedRef(n) => lookupClosed(gc,n) match {
        case Some(ed: ExprDecl) =>
          if (!ed.mutable) fail("assignment to immutable field")
        case _ => fail("not an assignable field")
      }
      case Tuple(es) => es foreach check
      case ListValue(es) => es foreach check
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

  // ************ auxiliary functions for handling identifiers (sharing code for types and expressions)

  private def resolvePathO(gc: GlobalContext, p: Path)(implicit cause: SyntaxFragment): Option[(Path,NamedDeclaration)] = {
    val closedField = if (p.names.length == 1) {
      lookupClosed(gc,p.names.head) // p might actually be a local field that the parser couldn't disambiguate
    } else None
    closedField match {
      case Some(d) => Some((p, d))
      case None =>
        // multiple segments, or single segment that is not a closed reference
        gc.voc.lookupRelativePath(gc.currentParent,p)
    }
  }
  private def resolvePath(gc: GlobalContext, p: Path)(implicit cause: SyntaxFragment): (Path,NamedDeclaration) = {
    resolvePathO(gc,p) getOrElse {
      fail("unknown path")
    }
  }

  /** disambiguate single-segment identifiers that the parser may have left ambiguous
    * resolving can involve retrieving the declaration, which can be expensive; so we return it if we find one
    */
  private def resolveName(gc: GlobalContext, obj: Object)(implicit cause: SyntaxFragment): (Object,Option[NamedDeclaration]) = {
    obj match {
      case ClosedRef(n) =>
        // try finding local variable n in context
        if (gc.local.lookupO(n).isDefined) {
          return (VarRef(n),None)
        }
        // try finding n declared in current module
        if (gc.inPhysicalTheory) {
          val p = gc.currentParent/n
          gc.voc.lookupPathAndParents(p, Nil) match {
            case Some(d :: (par: Module) :: _) if par.closed =>
              // declaration in current, closed module
              return (obj,Some(d))
            case Some(d :: _) =>
              // if the current module is open, we must change this to an open reference
              return (OpenRef(p),Some(d))
            case _ =>
          }
        }
        // try finding n declared in included module
        lookupClosed(gc,n) match {
          case Some(d) =>
            return (obj,Some(d))
          case None =>
        }
        // try finding n in any parent theory
        gc.voc.lookupRelativePath(gc.currentParent,Path(List(n))) match {
          case Some((p,d)) =>
            // open reference n in parent theory
            (OpenRef(p),Some(d))
          case None =>
            // give up
            fail("unknown identifier " + n)
        }
      case _ => (obj,None)
    }
  }

  def lookupClosed(gc: GlobalContext, name: String)(implicit cause: SyntaxFragment): Option[NamedDeclaration] = {
    // lookup in all parts of current theory
    val ds = gc.theory.parts.flatMap {p =>
      gc.voc.lookupPath(p/name).toList
    }
    if (ds.isEmpty) return None
    // find the most defined one
    var res = ds.head
    ds.tail.foreach {d =>
      Declaration.compare(res,d) match {
        case Declaration.Subsumes | Declaration.Identical =>
        case Declaration.SubsumedBy => res = d
        case Declaration.Independent | Declaration.Clashing => fail("multiple incompatible declarations found")
      }
    }
    Some(res)
    // todo: lookup in enclosing module
  }

  private def checkOpenRef(gc: GlobalContext, r: OpenRef)(implicit cause: SyntaxFragment) = {
    val (pC, pd) = resolvePath(gc, r.path)
    // TODO check that base of open module is included into current scope
    val rC = OpenRef(pC)
    (rC,pd)
  }

  /** for replacing OwnedObj with Expr[s]Over or OpenRef because the parser cannot disambiguate these */
  // the type bound allows taking a Type or an Expression and returning the same
  // TODO: this must still do the OpenRef part, probably by recursively checking the owners for open modules
  private def correctFreeOwner[A >: Type with Expression](gc: GlobalContext, o: A): Option[A] = o match {
    case o: OwnedObject =>
      val pO = o.owner match {
        case OpenRef(p) => gc.voc.lookupModule(p).map {
          _ => p
        }
        case ClosedRef(n) => gc.theory.parts.map(_/n).find {p =>
          gc.voc.lookupModule(p).isDefined
        }
        case _ => None
      }
      pO map {p =>
        val le =  RegionalContext(p)
        o match {
          case o: OwnedType => ExprsOver(le,o.owned).copyFrom(o).asInstanceOf[A] // guaranteed to work, but needed by Scala compiler
          case o: OwnedExpr => ExprOver(le,o.owned).copyFrom(o).asInstanceOf[A]
        }
      }
    case _ => None
  }

  def inferOperator(gc: GlobalContext,op: Operator,ins: List[Type])(implicit cause: Expression): Type = {
    val param = Type.unknown()
    val possibleTypes = op.types:::op.polyTypes(param)
    val matchResults = possibleTypes.map {case f@FunType(expected,_) =>
      matchTypes(ProdType(expected), ProdType(ins)).map((f,_))
    }
    val matchingTypes = matchResults.flatMap(_.toList)
    if (matchingTypes.length == 0)
      fail("ill-typed operator")
    val outs = matchingTypes.map(_._1.out).distinct
    // infer return type if all possible types agree
    val out = if (outs.length == 1) outs.head else fail("cannot disambiguate operator")
    // find all unknowns that all possible types agree on
    var commonAssignments: TypeAssignments = matchingTypes.head._2
    matchingTypes.tail.foreach {case (_,next) => commonAssignments = commonAssignments intersect next}
    // if we found multiple assignments for the parameter of this operator, take their union
    val (paramAssignments, otherAssignments) = commonAssignments.partition(_._1 == param)
    val paramAssignment = if (paramAssignments.isEmpty) Nil else List((param, typeUnion(gc, paramAssignments.map(_._2))))
    // better take union than fail because of equality and + on lists
    assignAsMatched(paramAssignment:::otherAssignments)
    out
  }

  private type TypeAssignments = List[(UnknownType,Type)]
  /** checks if the types can be made equal by assigning to unknowns, returns those assignments */
  private def matchTypes(a: Type, b: Type): Option[TypeAssignments] = (a.skipUnknown,b.skipUnknown) match {
    case (a,b) if a == b => Some(Nil)
    case (u: UnknownType, k) if !u.known => Some(List((u,k)))
    case (k, u: UnknownType) if k.known && !u.known => Some(List((u,k)))
    case (a: TypeOperator, b: TypeOperator) =>
      if (a.getClass == b.getClass && a.children.length == b.children.length) {
        val mcs = (a.children zip b.children).map{case (c,d) => matchTypes(c,d)}
        if (mcs.forall(_.isDefined)) Some(mcs.flatMap(_.get)) else None
      } else
        None
    case _ => None
  }
  /** applies assignments returned by matchTypes */
  private def assignAsMatched(as: TypeAssignments) = as.distinct.foreach {case (u,a) =>
    u.set(a)
  }
  /** like matchTypes, but makes the assignments right away if matching is possible */
  private def equateTypes(a: Type, b: Type) = matchTypes(a,b) match {
    case Some(uas) => assignAsMatched(uas); true
    case None => false
  }
}

class MagicFunctions(gc: GlobalContext) {
  class MagicFunction(name: String) {
    def insert(owner: Expression,args: List[Expression]) = Application(owner.field(name),args)
    def unapply(tp: Type) = tp match {
      case ClassType(thy) => Checker.lookupClosed(gc.push(thy),name)(tp) match {
        case Some(d: ExprDecl) => Some((thy,d.tp))
        case _ => None
      }
      case _ => None
    }
  }
  object listElement extends MagicFunction("elemAt")
  object iteration extends MagicFunction("elements")
  object application extends MagicFunction("apply")
  class projection(n: Int) extends MagicFunction("component_"+n)
  object evaluation extends MagicFunction("eval")
}