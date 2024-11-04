package info.kwarc.p

import SyntaxFragment.matchC

object Checker {
  private val debug = true

  case class Error(cause: SyntaxFragment,msg: String) extends PError(cause.loc + ": " + msg + " while checking " + cause.toString)
  def fail(m: String)(implicit cause: SyntaxFragment) = throw Error(cause,m)

  def checkProgram(p: Program): Program = matchC(p) {
    case Program(voc,mn) =>
      val env = GlobalEnvironment("")
      val vocC = checkDeclarationsAndFlatten(env, p.voc)
      val envC = GlobalEnvironment(Module.anonymous(vocC))
      val mnC = checkExpression(envC,mn,AnyType)
      Program(vocC, mnC)
  }

  def checkDeclaration(env: GlobalEnvironment, decl: Declaration): Declaration = {
    if (debug) println("checking: " + decl)
    implicit val cause = decl
    val declC = decl match {
      case m:Module =>
        // checking will try to merge declarations of the same name, so no uniqueness check needed
        val envM = env.add(m.copy(decls = Nil)).enter(m.name)
        val declsC = checkDeclarationsAndFlatten(envM, m.decls)
        // check if this module has definitions for every abstract declaration in a realized theory
        val defines = declsC.collect {
          case sd: SymbolDeclaration if sd.dfO.isDefined => sd.name
        }
        declsC.foreach {
          case id: Include if id.realize => env.voc.lookupModule(id.dom).get.undefined.foreach {sd =>
            if (!defines.contains(sd.name))
              fail("missing definition of " + id.dom/sd.name)
          }
          case _ =>
        }
        m.copy(decls = declsC)
        // TODO instance creation may occur before or while a theory is checked - needs 2-phase approach
      case id: Include =>
        if (id.dom != null) {
          val domC = checkTheoryPath(env, id.dom)(id)
          // TODO: what about includes of open theories
          val dfOC = id.dfO map {d => checkExpression(env,d,ClassType(Theory(domC)))}
          Include(domC,dfOC,id.realize)
        } else id.dfO match {
          case None => fail("untyped include")
          case Some(df) =>
            // infer domain from definiens
            val (dfC,dfI) = inferExpression(env,df)
            dfI match {
              case ClassType(Theory(List(p))) =>
                Include(p, Some(dfC), id.realize)
              case _ => fail("domain not an atomic theory")
            }
        }
        // TODO check purity of definiens
      case sd: SymbolDeclaration =>
        checkSymbolDeclaration(env, env.currentParent, sd)
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

  private def checkDeclarationsAndFlatten(env: GlobalEnvironment, decls: List[Declaration]): List[Declaration] = {
    /* a FIFO queue of lists of declarations that must be flattened
     * Later on included lists of declarations will be prefixed with that flag negated and the definiens of the include.
     * It would be equivalent to keep a List[Declaration] instead of what is essentially a list of lists of declarations
     * if the former always holds the concatenation of the latter.
     * But our implementation is more efficient because it avoids that copying lists.
     */
    // initially, we need to flatten the original list, which must be checked but not translated
    var todo = List(FlattenInput(decls,true,None))
    var envC = env // will change as we process declarations
    // adds a declaration to the result, possibly merging with an existing one
    // returns true if added (redundant otherwise)
    def add(d: Declaration, current: FlattenInput): Boolean = {
      val dT = current.alsoTranslate match {
        case None => d
        case Some(o) => OwnerSubstitutor(o, d)
      }
      val old = envC
      val existing = envC.parentDecl.decls.view.map {e =>
        (e,Declaration.compare(e,dT))
      }.find {case (e,c) => c != Declaration.Independent}
      existing match {
        case None =>
          if (debug) println("new declaration: " + dT)
          envC = envC.add(dT)
        case Some((e,r)) => r match {
          case Declaration.Identical | Declaration.Subsumes =>
            if (debug) println("subsumed declaration: " + dT)
          // new declaration is redundant: nothing to do
          case Declaration.SubsumedBy =>
            // old declaration is redundant: mark it for later removal
            e.redundant = true
            if (debug) println("subsuming declaration: " + dT)
            envC = envC.add(dT)
          case Declaration.Clashing =>
            // declarations could be incompatible; further comparison needed
            fail("declaration clash")(d)
          case Declaration.Independent =>
            throw IError("impossible case")
        }
      }
      envC != old
    }
    // skip empty todos, repeat until no todos are left
    while ({todo = todo.dropWhile(_.decls.isEmpty); todo.nonEmpty}) {
      // take off the first among the todos
      val current = todo.head
      val d = current.decls.head
      todo = current.tail :: todo.tail
      // check it if necessary
      val dC = if (current.alsoCheck) checkDeclaration(envC, d) else d
      // flatten the current declaration and move the result to 'done'
      val changed = add(dC, current)
      // if it is a non-redundant include, queue the body as well
      if (changed) dC match {
        case Include(p, dfO, _) =>
          val m: Module = env.voc.lookupModule(p).get
          todo ::= FlattenInput(m.decls, false, dfO)
        case _ =>
      }
    }
    // reverse 'done' while skipping redundant declarations
    var result: List[Declaration] = Nil
    envC.parentDecl.decls.foreach {d =>
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
  private def checkSymbolDeclaration(env: GlobalEnvironment, parent: Path, sd: SymbolDeclaration): SymbolDeclaration = {
    implicit val cause = sd
    env.voc.lookupPath(parent/sd.name) match {
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
          checkType(env, sd.tp, abs.tp)
        }
        sd match {
          case sd: ExprDecl =>
            // definition = Undefined: nothing to do
            // definition = Defined: check against type
            val dfC = sd.dfO.map {df => checkExpression(env,df,tpC)}
            sd.copy(tp = tpC,dfO = dfC)
          case sd: TypeDecl =>
            val dfC = sd.dfO.map {df => checkType(env, df, tpC)}
            sd.copy(tp = tpC,dfO = dfC)
        }
      case Some(_) =>
        // Other: error
        fail("name is inherited but not a symbol")
      case None =>
        // No: check declaration without inherited type
        sd match {
          case td: TypeDecl =>
            val tpC = checkType(env,td.tp)
            val dfOC = td.dfO map {df => checkType(env,df,tpC)}
            td.copy(tp = tpC,dfO = dfOC)
          case sd: ExprDecl =>
            val (tpC,dfC) = if (!sd.tp.known) {
              sd.dfO match {
                case None => fail("untyped declaration")
                case Some(df) =>
                  val (c,i) = inferExpression(env,df)
                  (i,Some(c))
              }
            } else {
              val tC = checkType(env,sd.tp)
              val dC = sd.dfO map {d =>
                checkExpression(env,d,tC)
              }
              (tC,dC)
            }
            sd.copy(tp = tpC,dfO = dfC)
        }
    }
  }

  def checkEnvironment(env: GlobalEnvironment, le: LocalEnvironment): LocalEnvironment = {
    val thyC = checkTheory(env,le.theory)(le.theory)
    val ctxC = checkContext(env.push(thyC), le.context, false, false)
    LocalEnvironment(thyC,ctxC)
  }
  def checkTheoryPath(env: GlobalEnvironment, p: Path)(implicit cause: SyntaxFragment) = {
    resolvePath(env, p) match {
      case (pC, m: Module) => pC
      case _ => fail("not a module")
    }
  }
  def checkTheory(env: GlobalEnvironment, thy: Theory)(implicit cause: SyntaxFragment) = {
    val partsC = thy.parts.map {p => checkTheoryPath(env,p)}
    val flat = partsC.flatMap {p => env.voc.lookupModule(p).get.supers}.distinct
    // TODO: check compatibility of all parts with each other
    val thyC = Theory(flat)
    thy.isFlat = true
    thyC
  }
  def checkContext(env: GlobalEnvironment,c: Context,allowDefinitions: Boolean,allowMutable: Boolean): Context = {
    var envL = env
    val declsC = c.decls.map {vd =>
      val vdC = checkVarDecl(envL,vd,allowDefinitions,allowMutable)
      envL = envL.add(vdC)
      vdC
    }
    Context(declsC)
  }

  def checkVarDecl(env: GlobalEnvironment,vd: VarDecl,allowDefinitions: Boolean,allowMutable: Boolean): VarDecl = {
    implicit val cause = vd
    if (vd.mutable && !allowMutable) fail("mutable variable not allowed here")
    if (vd.defined && !allowDefinitions) fail("defined variable not allowed here")
    val tpC = if (vd.tp.known) {
      checkType(env,vd.tp)
    } else vd.tp
    val dfC = vd.dfO map {d => checkExpression(env,d,tpC)}
    VarDecl(vd.name,tpC.skipUnknown,dfC,vd.mutable)
  }

  /** theory a subsumbed by b */
  def isSubtheory(a: Theory, b: Theory) = {
    a.parts.forall(p => b.parts.contains(p))
  }
  /** context a subsumed by b */
  def isSubcontext(a: Context, b: Context) = {
    a.decls.forall(d => b.decls.contains(d))
  }
  /** environment a subsumed by b */
  def isSubenvironment(a: LocalEnvironment, b: LocalEnvironment) = {
    isSubtheory(a.theory, b.theory) && isSubcontext(a.context,b.context)
  }

  // ***************** Types **************************************
  def checkType(env: GlobalEnvironment,tp: Type, bound: Type): Type = {
    val tpC = checkType(env,tp)
    checkSubtype(env, tpC, bound)(tp)
    tpC
  }
  def checkType(env: GlobalEnvironment, tpA: Type): Type = {
    implicit val cause = tpA
    correctFreeOwner(env, tpA).foreach {corrected => return checkType(env, corrected)}
    // tp != tA only if tpA is an unresolved reference
    val (tpR, sdCached) = resolveName(env, tpA)
    val tp = tpR match {
      case t: Type => t
      case _ => fail("not a type")
    }
    matchC(tp) {
      case r: OpenRef =>
        val (rC,rd) = sdCached match {
          case Some(d) => (r, d)
          case _ => checkOpenRef(env,r)
        }
        rd match {
          case td: TypeDecl => tp
          case m: Module if r.via.isEmpty =>
            // todo: pushout if via.isDefined
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
        val (ownerC, ownerI) = inferExpression(env, owner)
        ownerI match {
          case ClassType(d) =>
            val envO = env.push(d)
            val tpC = checkType(envO, tp)
            OwnedType(ownerC, tpC)
          case _ => fail("owner must be an instance")
        }
      case _: BaseType => tp
      case tp: TypeOperator =>
        tp.children.foreach(c => checkType(env,c))
        tp
      case ClassType(thy) =>
        val thyC = checkTheory(env, thy)(tp)
        ClassType(thyC)
      case ExprsOver(thy, q) =>
        val thyC = checkEnvironment(env, thy)
        val qC = checkType(env.push(thy), q)
        ExprsOver(thyC, qC)
      case u: UnknownType =>
        if (u.known)
          checkType(env, u.tp)
        else
          fail("uninferred omitted type")
    }
  }

  /** sub subtype of sup */
  def checkSubtype(env: GlobalEnvironment,sub: Type,sup: Type)(implicit cause: SyntaxFragment): Unit = {
    val union = typeUnion(env,sub,sup)
    if (union != sup) // Theory overrides equals
      fail(s"found: $sub; expected: $sup")
  }

  /** flattened if the inputs are */
  def typeUnion(env: GlobalEnvironment,tps: List[Type])(implicit cause: SyntaxFragment): Type = {
    var res: Type = EmptyType
    tps.foreach {tp => res = typeUnion(env,res,tp)}
    res
  }

  /** least common supertype
    * flattened if the inputs are
    */
    //TODO type bounds
  def typeUnion(env: GlobalEnvironment,a: Type,b: Type)(implicit cause: SyntaxFragment): Type = {
    (a,b) match {
      case (a,b) if a == b => a
      case (AnyType,_) | (_,AnyType) => AnyType
      case (EmptyType,t) => t
      case (t,EmptyType) => t
      case (IntType,RatType) | (RatType,IntType) => RatType
      case (ListType(a),ListType(b)) => ListType(typeUnion(env,a,b))
      case (ProdType(as),ProdType(bs)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeUnion(env,x,y)}
        ProdType(abs)
      case (FunType(as,o),FunType(bs,p)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeIntersection(env,x,y)}
        val op = typeUnion(env,o,p)
        FunType(abs,op)
      case (ExprsOver(aT,u), ExprsOver(bT, v)) =>
        if (aT != bT) fail("not quoted in the same context")
        val thyU = theoryUnion(env, aT.theory, bT.theory)
        val ctxU = (aT.context.decls ::: bT.context.decls).distinct
        val scopeU = LocalEnvironment(thyU,Context(ctxU))
        val varNames = ctxU.map(_.name)
        if (varNames.distinct != varNames) fail("incompatible variable names")
        // aT-expression of type u or bT-expression of type v, i.e., expression over union of union type
        ExprsOver(scopeU, typeUnion(env.push(scopeU), u, v))
      case (ClassType(aT), ClassType(bT)) =>
        // model of aT or model of bT, i.e., model of intersection
        val i = theoryIntersection(env,aT,bT)
        if (i.parts.isEmpty) AnyType else ClassType(i)
      case _ =>
        val aN = typeNormalize(env, a)
        val bN = typeNormalize(env, b)
        if (aN != a || bN != b)
          typeUnion(env, aN, bN)
        else
          AnyType
    }
  }

  /** greatest common subtype
    * flattened if the inputs are
    */
   //TODO type bounds
  def typeIntersection(env: GlobalEnvironment, a: Type, b: Type)(implicit cause: SyntaxFragment): Type = {
    (a,b) match {
      case (a,b) if a == b => a
      case (AnyType,t) => t
      case (t,AnyType) => t
      case (EmptyType,_) | (_,EmptyType) => EmptyType
      case (IntType,RatType) | (RatType,IntType) => IntType
      case (ListType(a),ListType(b)) => ListType(typeIntersection(env,a,b))
      case (ProdType(as),ProdType(bs)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeIntersection(env,x,y)}
        ProdType(abs)
      case (FunType(as,o),FunType(bs,p)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeUnion(env,x,y)}
        val op = typeIntersection(env,o,p)
        FunType(abs,op)
      case (ExprsOver(aT,u), ExprsOver(bT, v)) =>
        // aT-expression of type u and bT-expression of type v, i.e., expression over the intersection of intersection type
        val thyI = theoryIntersection(env, aT.theory, bT.theory)
        val ctxI = aT.context.decls intersect bT.context.decls // todo: not necessarily well-formed
        val scopeI = LocalEnvironment(thyI, Context(ctxI))
        ExprsOver(scopeI, typeIntersection(env.push(scopeI), u, v)) // todo: u,v might use variables
      case (ClassType(aT), ClassType(bT)) =>
        // model of aT and of bT, i.e., model of the union
        ClassType(theoryUnion(env,aT,bT))
      case _ =>
        val aN = typeNormalize(env, a)
        val bN = typeNormalize(env, b)
        if (aN != a || bN != b)
          typeIntersection(env, aN, bN)
        else
          EmptyType
    }
  }

  /** union (colimit) of theories */
  def theoryUnion(env: GlobalEnvironment, a: Theory, b: Theory): Theory = {
    val pqs = (a.parts ::: b.parts).distinct //TODO error if not compatible
    val thy = Theory(pqs)
    thy.isFlat = a.isFlat && b.isFlat // flat if the inputs are
    thy
  }

  /** intersection of theories: the union of all common includes */
  def theoryIntersection(env: GlobalEnvironment, a: Theory, b: Theory): Theory = {
    val pqs = a.parts intersect b.parts // TODO remove definiens if not the same
    val thy = Theory(pqs)
    thy.isFlat = a.isFlat && b.isFlat // flat if the inputs are
    thy
  }

  /** normalizes a type: definitions expanded, but not flattened */
  def typeNormalize(env: GlobalEnvironment, tp: Type): Type = {
    implicit val cause = tp
    def n(t: Type) = typeNormalize(env, t)
    def f(t: Theory) = checkTheory(env, t)
    matchC(tp) {
      case ClosedRef(f) => lookupClosed(env, f) match {
        case Some(td: TypeDecl) => td.dfO match {
          case Some(df) => n(df)
          case None => tp
        }
        case _ => fail("illegal type")(tp) // impossible if tp is checked
      }
      case OpenRef(p, ownO) =>
        env.voc.lookupPath(p) match {
          case Some(td: TypeDecl) => td.dfO match {
            case None => tp
            case Some(df) =>
              var d = df
              ownO foreach {o => d = OwnedType(o,d)}
              n(d)
          }
          case _ => fail("illegal type")(tp) // impossible if tp is checked
        }
      case OwnedType(own, t) =>
        val tpS = OwnerSubstitutor(own, t)
        if (tpS != tp) typeNormalize(env, tpS) else tpS
      case _: BaseType => tp
      case FunType(as,a) => FunType(as map n, n(a))
      case ProdType(as) => ProdType(as map n)
      case ListType(a) => ListType(n(a))
      case OptionType(a) => OptionType(n(a))
      case ClassType(sc) => ClassType(f(sc))
      case ExprsOver(sc, t) =>
        val thyN = f(sc.theory)
        ExprsOver(LocalEnvironment(thyN, sc.context), n(t))
      case u: UnknownType => if (u.known) n(u.tp) else u
    }
  }

  // ***************** Expressions **************************************
  /** checks an expression against an expected type
    *
    * This is helpful for infering omitted information in introduction forms from their expected type.
    * In most cases, this defers to type inference and subtype checking.
    */
  def checkExpression(env: GlobalEnvironment,exp: Expression,tp: Type): Expression = {
    implicit val cause = exp
    correctFreeOwner(env, exp).foreach {corrected => return checkExpression(env, corrected, tp)}
    correctFreeOwner(env, tp).foreach {corrected => return checkExpression(env, exp, corrected)}
    val tpN = typeNormalize(env, tp)
    val eC = (exp,tpN) match {
      case (ListValue(es),ListType(t)) =>
        val esC = es.map(e => checkExpression(env,e,t))
        ListValue(esC)
      case (Tuple(es),ProdType(ts)) =>
        if (es.length != ts.length) fail("wrong number of components in tuple")
        val esC = (es zip ts) map {case (e,t) => checkExpression(env,e,t)}
        Tuple(esC)
      case (Lambda(insG,outG),FunType(insE,outE)) =>
        if (insG.decls.length != insE.length) fail("wrong number of variables in lambda")
        (insG.decls zip insE).foreach {case (inG,inE) =>
          inG.tp match {
            case u: UnknownType =>
              u.set(inE)
            case _ =>
              checkSubtype(env, inE, inG.tp)
          }
        }
        val insC = checkContext(env,insG,false,false)
        val outC = checkExpression(env.add(insC),outG,outE)
        Lambda(insC,outC)
      case (OwnedExpr(oe, e), OwnedType(ot, tp)) if oe == ot =>
        val (oC,oI) = inferExpression(env, oe)
        oI match {
          case ClassType(d) =>
            val eC = checkExpression(env.push(d), e, tp)
            OwnedExpr(oC, eC)
          case _ => fail("owner must be class type")
        }
      case (ExprOver(scE,e), ExprsOver(scT, tp)) =>
        val scTC = checkEnvironment(env, scT)
        if (scE != null) {
          if (!isSubenvironment(scE, scTC)) fail("quoted scope not part of expected type")
        }
        val eC = checkExpression(env.push(scTC), e, tp)
        ExprOver(scTC, eC)
      case (Application(op: BaseOperator,args),_) if !op.tp.known =>
        val (argsC,argsI) = args.map(a => inferExpression(env,a)).unzip
        val opTp = FunType(argsI,tpN)
        val opC = checkExpression(env,op,opTp)
        Application(opC,argsC)
      case (BaseOperator(op,opTp),FunType(ins,out)) =>
        opTp match {
          case u: UnknownType =>
            val outI = inferOperator(env,op,ins)
            checkSubtype(env,outI,out)
            u.set(tpN)
          case _ =>
            checkSubtype(env,opTp,tpN)
        }
        BaseOperator(op,tpN)
      case _ =>
        val (eC,eI) = inferExpression(env,exp)
        matchTypes(eI,tpN) match {
          case Some(us) =>
            // infer unknown types
            us.distinct.foreach {case (u,a) =>
              u.set(a)
            }
          case _ =>
            checkSubtype(env,eI,tpN)
        }
        eC
    }
    eC.copyFrom(exp)
    eC
  }

  /** like [[inferExpression]] but with the type normalized */
  def inferExpressionNorm(env: GlobalEnvironment,e: Expression): (Expression,Type) = {
    val (eC,eI) = inferExpression(env, e)
    (eC, typeNormalize(env,eI))
  }

  /** checks an expression and infers its type
    *
    * This defers to [[checkExpression]] if it knows the expected type.
    */
  def inferExpression(env: GlobalEnvironment,expA: Expression): (Expression,Type) = {
    implicit val cause = expA
    val mf = new MagicFunctions(env)
    // exp != expA only if exp is an unresolved reference
    val (expR, sdCached) = resolveName(env, expA)
    val exp = expR match {
      case e: Expression => e
      case _ => fail("not an expression")
    }
    correctFreeOwner(env, expA).foreach {corrected => return inferExpression(env, corrected)}
    // check exp and infer its type
    val (expC,expI) = exp match {
      case e: BaseValue => (e,e.tp)
      case op: BaseOperator =>
        if (!op.tp.known) {
          fail("cannot infer type of operator")
        }
        val ft = typeNormalize(env,op.tp) match {
          case ft: FunType => ft
          case _ => fail("operator type not a function")
        }
        val out = inferOperator(env,op.operator,ft.ins)
        checkSubtype(env,out,ft.out)(exp)
        (BaseOperator(op.operator,ft),op.tp)
      case r: OpenRef =>
        val (rC,rd) = sdCached match {
          case Some(d) => (r, d)
          case _ => checkOpenRef(env,r)
        }
        rd match {
          case ed: ExprDecl =>
            val rI = rC.via match {
              case None => ed.tp
              case Some(v) => OwnedType(v, ed.tp)
            }
            (rC, rI)
          case _ => fail(s"$r is not an expression")
        }
      case ClosedRef(n) =>
        sdCached match {
          case Some(ed: ExprDecl) => (exp, ed.tp)
          case _ => fail("not an expression")
        }
      case OwnedExpr(owner, e) =>
        val (ownerC, ownerI) = inferExpression(env, owner)
        ownerI match {
          case ClassType(d) =>
            val envO = env.push(d)
            val (eC, eI) = inferExpression(envO, e)
            (OwnedExpr(ownerC, eC), OwnedType(ownerC, eI))
          case _ => fail("owner must be an instance")
        }
      case VarRef(n) =>
        (exp,env.context.lookup(n).tp)

      case Instance(thy,ds) =>
        val (thyC, thyD) = resolvePath(env, thy)
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
            checkSymbolDeclaration(env, thyC, sd)
          case i: Include =>
            fail("include unsupported")(i)
        }
        mod.undefined.foreach {sd =>
          if (!definedNames.contains(sd.name)) fail("instance must define " + sd.name)
        }
        (Instance(thyC,dsC),ClassType(Theory(thyC)))
      case ExprOver(sc,q) =>
        val scC = checkEnvironment(env,sc)
        val (qC,qI) = inferExpression(env.push(scC),q)
        (ExprOver(scC,qC),ExprsOver(scC,qI))
      case Eval(e) =>
        if (env.locals.isEmpty) fail("eval outside quotation")
        val (eC,eI) = inferExpressionNorm(env.pop(),e)
        eI match {
          case ExprsOver(eT,q) =>
            if (!isSubenvironment(eT, env.currentLocal)) fail("quoted over wrong theory")
            (Eval(eC),q)
          case mf.evaluation(_,a) =>
            (mf.evaluation.insert(eC, Nil), a)
          case _ => fail("not a quoted expression")
        }
      case Lambda(ins,bd) =>
        val insC = checkContext(env,ins,false,false)
        val inTypes = insC.decls.map(_.tp)
        val (bdC,bdI) = inferExpression(env.add(insC),bd)
        (Lambda(insC,bdC),FunType(inTypes,bdI))
      case Application(f,as) =>
        f match {
          case op: BaseOperator if !op.tp.known =>
            // for an operator of unknown type, we need to infer the argument types first
            val (asC,asI) = as.map(a => inferExpression(env,a)).unzip
            val out = inferOperator(env,op.operator,asI)
            val opC = op.copy(tp = FunType(asI,out))
            (Application(opC,asC),out)
          case f =>
            val (fC,fI) = inferExpressionNorm(env,f)
            val (fM,ins,out) = fI match {
              case FunType(i,o) => (fC,i,o)
              case ProdType(ys) =>
                as match {
                  case List(IntValue(i)) =>
                    // projections are parsed as applications
                    return inferExpression(env, Projection(f,i).copyFrom(exp))
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
            val asC = (as zip ins).map {case (a,i) => checkExpression(env,a,i)}
            (Application(fM,asC),out)
        }
      case Tuple(es) =>
        val (esC,esI) = es.map(e => inferExpression(env,e)).unzip
        (Tuple(esC),ProdType(esI))
      case Projection(tup, p) =>
        val mfp = new mf.projection(p)
        val (tupC,tupI) = inferExpressionNorm(env,tup)
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
        val (esC,esI) = es.map(e => inferExpression(env,e)).unzip
        val eI = typeUnion(env,esI)
        (ListValue(esC),ListType(eI))
      case ListElem(l, p) =>
        val (lC,lI) = inferExpressionNorm(env, l)
        val pC = checkExpression(env, p, IntType)
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
           val (eC,eI) = inferExpression(env, e)
           (OptionValue(eC), OptionType(eI))
         }
      case Block(es) =>
        var envL = env // local environment, includes variables seen in the block so far
        var eTp: Type = UnitType // type of the last seen expression in the block
        val esC = es.map {e =>
          val (eC,eI) = inferExpression(envL, e)
          eTp = eI
          eC match {
            case vd:VarDecl =>
              val vdNoDef = if (vd.defined && vd.mutable) vd.copy(dfO = None) else vd
              envL = envL.add(vdNoDef)
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
              val (vlC,vlI) = inferExpression(env, vl)
              (vlI, Some(vlC))
          }
        } else {
          val tpC = checkType(env, tp)
          val vlC = vlO map {vl => checkExpression(env,vl,tp)}
          (tpC,vlC)
        }
        (VarDecl(n,tpC,vlC,mut),UnitType)
      case Assign(e,df) =>
        val (eC,eI) = inferExpression(env, e)
        val dfC = checkExpression(env,df,eI)
        checkAssignable(env,e)
        (Assign(eC,dfC),UnitType)
      case While(cond,bd) =>
        val condC = checkExpression(env, cond, BoolType)
        val bdC = checkExpression(env, bd, AnyType)
        (While(condC, bdC), UnitType)
      case IfThenElse(cond,thn, elsO) =>
        val condC = checkExpression(env, cond, BoolType)
        val (thnC,thnI) = inferExpression(env, thn)
        val (elsOC, eI) = elsO match {
          case Some(els) =>
            val (elsC, elsI) = inferExpression(env, els)
            val u = typeUnion(env, thnI, elsI)
            if (u == AnyType) fail("branches have incompatible types")
            (Some(elsC), u)
          case None => (None,UnitType)
        }
        (IfThenElse(condC, thnC, elsOC), eI)
      case For(n, range, bd) =>
        val (rangeC,rangeI) = inferExpressionNorm(env, range)
        val (rangeM, nTp) = rangeI match {
          case ListOrUnknownType(t) => (rangeC, t)
          case mf.iteration(_,ListType(t)) => (mf.iteration.insert(rangeC, Nil), t)
          case _ => fail("not iterable")
        }
        val bdC = checkExpression(env.add(VarDecl(n,nTp)), bd, AnyType)
        (For(n, rangeM, bdC), UnitType)
    }
    expC.copyFrom(exp)
    (expC,expI)
  }

  private def checkAssignable(env: GlobalEnvironment, target: Expression): Unit = {
    def check(t: Expression) = checkAssignable(env, t)
    implicit val cause = target
    target match {
      case VarRef("") => // anonyomous variable
      case VarRef(n) =>
        val vd = env.context.lookup(n)
        if (!vd.mutable) fail("variable not mutable")
      case ClosedRef(n) => lookupClosed(env,n) match {
        case Some(ed: ExprDecl) =>
          if (!ed.mutable) fail("assignment to immutable field")
        case _ => fail("not an assignable field")
      }
      case Tuple(es) => es foreach check
      case ListValue(es) => es foreach check
      case eo: ExprOver => EvalTraverser(eo) {e => check(e); e}
      case Application(OpenRef(r,None),es) =>
        env.voc.lookupPath(r) match {
          case Some(ed: ExprDecl) if ed.dfO.isEmpty =>
          case _ => fail("function application not assignable")
        }
        es foreach check
      case _ => fail("expression not assignable")
    }
  }

  // ************ auxiliary functions for handling identifiers (sharing code for types and expressions)

  private def resolvePathO(env: GlobalEnvironment, p: Path)(implicit cause: SyntaxFragment): Option[(Path,NamedDeclaration)] = {
    val closedField = if (p.names.length == 1) {
      lookupClosed(env,p.names.head) // p might actually be a local field that the parser couldn't disambiguate
    } else None
    closedField match {
      case Some(d) => Some((p, d))
      case None =>
        // multiple segments, or single segment that is not a closed reference
        env.voc.lookupRelativePath(env.currentParent,p)
    }
  }
  private def resolvePath(env: GlobalEnvironment, p: Path)(implicit cause: SyntaxFragment): (Path,NamedDeclaration) = {
    resolvePathO(env,p) getOrElse {
      fail("unknown path")
    }
  }

  /** disambiguate single-segment identifiers that the parser may have left ambiguous
    * resolving can involve retrieving the declaration, which can be expensive; so we return it if we find one
    */
  private def resolveName(env: GlobalEnvironment, obj: Object)(implicit cause: SyntaxFragment): (Object,Option[NamedDeclaration]) = {
    obj match {
      case ClosedRef(n) =>
        // try finding local variable n in context
        if (env.context.lookupO(n).isDefined) {
          return (VarRef(n),None)
        }
        // try finding n declared in current module
        if (env.inPhysicalTheory) {
          val p = env.currentParent/n
          env.voc.lookupPathAndParents(p, Nil) match {
            case Some(d :: (par: Module) :: _) if par.closed =>
              // declaration in current, closed module
              return (obj,Some(d))
            case Some(d :: _) =>
              // if the current module is open, we must change this to an open reference
              return (OpenRef(p,None),Some(d))
            case _ =>
          }
        }
        // try finding n declared in included module
        lookupClosed(env,n) match {
          case Some(d) =>
            return (obj,Some(d))
          case None =>
        }
        // try finding n in any parent theory
        env.voc.lookupRelativePath(env.currentParent,Path(List(n))) match {
          case Some((p,d)) =>
            // open reference n in parent theory
            (OpenRef(p,None),Some(d))
          case None =>
            // give up
            fail("unknown identifier " + n)
        }
      case _ => (obj,None)
    }
  }

  def lookupClosed(env: GlobalEnvironment, name: String)(implicit cause: SyntaxFragment): Option[NamedDeclaration] = {
    // lookup in all parts of current theory
    val ds = env.theory.parts.flatMap {p =>
      env.voc.lookupPath(p/name).toList
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

  private def checkOpenRef(env: GlobalEnvironment, r: OpenRef)(implicit cause: SyntaxFragment) = {
    val (pC, pd) = resolvePath(env, r.path)
    val viaOC = r.via map {v =>
      val base = env.voc.lookupModule(pC.up).get.base
      // TODO empty viaO must be treated like identity morphism
      checkExpression(env, v, ClassType(Theory(base)))
    }
    val rC = OpenRef(pC, viaOC)
    (rC,pd)
  }

  /** for replacing OwnedObj with Expr[s]Over because the parser cannot disambiguate these */
  // the type bound allows taking a Type or an Expression and returning the same
  private def correctFreeOwner[A >: Type with Expression](env: GlobalEnvironment, o: A): Option[A] = o match {
    case o: OwnedObject =>
      val pO = o.owner match {
        case OpenRef(p,None) => env.voc.lookupModule(p).map {
          _ => p
        }
        case ClosedRef(n) => env.theory.parts.map(_/n).find {p =>
          env.voc.lookupModule(p).isDefined
        }
        case _ => None
      }
      pO map {p =>
        val le = LocalEnvironment(p)
        o match {
          case o: OwnedType => ExprsOver(le,o.owned).copyFrom(o).asInstanceOf[A] // guaranteed to work, but needed by Scala compiler
          case o: OwnedExpr => ExprOver(le,o.owned).copyFrom(o).asInstanceOf[A]
        }
      }
    case _ => None
  }

  def inferOperator(env: GlobalEnvironment,op: Operator,ins: List[Type])(implicit cause: Expression): Type = {
    val possibleTypes = op.types:::op.polyTypes(Type.unknown)
    val matchResults = possibleTypes.map {case f@FunType(expected,_) =>
      matchTypes(ProdType(expected), ProdType(ins)).map((f,_))
    }
    val matchingTypes = matchResults.flatMap(_.toList)
    if (matchingTypes.length == 0)
      fail("ill-typed operator")
    if (matchingTypes.length > 1)
      fail("cannot disambiguate operator")
    val (tp,us) = matchingTypes.head
    us.distinct.foreach {case (u: UnknownType, a) =>
      val ua = if (u.known) typeUnion(env, u.tp, a) else a // better take union than fail because of equality and + on lists
      if (u.known && ua == AnyType)
        fail("incompatible types")
      u.set(a)
    }
    tp.out
  }

  /** if the types can be made equal, by assigning to unknowns, the assignments */
  private def matchTypes(a: Type, b: Type): Option[List[(UnknownType,Type)]] = (a.skipUnknown,b.skipUnknown) match {
    case (u: UnknownType, k) if !u.known => Some(List((u,k)))
    case (k, u: UnknownType) if k.known && !u.known => Some(List((u,k)))
    case (a: TypeOperator, b: TypeOperator) =>
      if (a.getClass == b.getClass && a.children.length == b.children.length) {
        val mcs = (a.children zip b.children).map{case (c,d) => matchTypes(c,d)}
        if (mcs.forall(_.isDefined)) Some(mcs.flatMap(_.get)) else None
      } else
        None
    case (a,b) => if (a == b) Some(Nil) else None
  }
}

class MagicFunctions(env: GlobalEnvironment) {
  class MagicFunction(name: String) {
    def insert(owner: Expression,args: List[Expression]) = Application(owner.field(name),args)
    def unapply(tp: Type) = tp match {
      case ClassType(thy) => Checker.lookupClosed(env.push(thy),name)(tp) match {
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