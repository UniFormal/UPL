package info.kwarc.p

import SyntaxFragment.keepRef

object Checker {
  case class Error(cause: SyntaxFragment,msg: String) extends PError(cause.loc + ": " + msg + " while checking " + cause.toString)

  def checkProgram(p: Program): Program = keepRef(p) {
    case Program(v,m) =>
      val env = StaticEnvironment(p)
      val envL = checkDeclaration(env, v)
      val mC = checkExpression(envL,m,AnyType)
      Program(envL.voc, mC)
  }

  def checkDeclarations(env: StaticEnvironment, decls: List[Declaration]): StaticEnvironment = {
    var envC = env
    decls.foreach {d =>
      envC = checkDeclaration(envC, d)
    }
    envC
  }

  def checkDeclaration(env: StaticEnvironment, decl: Declaration): StaticEnvironment = {
    decl match {
      case nd: HasDeclarations[_] =>
        nd.decls.groupBy(_.nameO).foreach {case (n,ds) =>
          if (n.isDefined && ds.length > 1) {
            throw Error(decl,"name already defined: " + n.get)
          }
        }
      case _ =>
    }
    decl match {
      case Vocabulary(ds) =>
        if (env.parent.isRoot)
          checkDeclarations(env, ds)
        else
          throw Error(decl, "vocabulary not allowed as nested declaration")
      case m@Module(n, open, ds) =>
        val envC = checkDeclarations(env.enter(n), ds).leave
        if (open) {
          ds.foreach {
            case hd: HasDefiniens[_] if hd.dfO.isEmpty => throw Error(hd, "undefined declaration in open module")
            case _ =>
          }
        } else {
          // includes have been flattened already
          val supers = ds.flatMap {
            case i:Include => i.dom.parts
            case _ => Nil
          }.distinct
          m.supers = supers
          // TODO check realizations
        }
        envC
      case id@Include(dom, dfO, rz) =>
        val idC = if (dom != null) {
          val domC = flatten(env,dom)(decl)
          val dfOC = dfO map {d => checkExpression(env,d,ClassType(domC))}
          Include(domC,dfOC,rz)
        } else dfO match {
          case None => throw Error(id,"untyped include")
          case Some(df) =>
            // infer domain from definiens
            val (dfC,dfI) = inferExpression(env,df)
            dfI match {
              case ClassType(t) =>
                Include(t, Some(dfC), rz)
              case _ => throw Error(id, "domain not a theory")
            }
        }
        env.update(env.parent, id, idC)
      case cd @ Class(n, ds) =>
        val supsC = sups.map(t => checkType(env, t))
        val supsClasses = supsC.map {
          case sup @ TypeRef(s) =>
            (sup, env.voc.lookupClass(s, Error(sup, "not a class type")))
          case sup => throw Error(sup, "not a class type")
        }
        // flattening the supertypes
        val supsF = supsClasses.flatMap {case (sup,supClass) => sup::supClass.supers}.distinct
        val cd1 = cd.copy(supers = supsF)
        var envL = env.update(env.parent, cd, cd1) // need to update this before checking the declarations
        envL = envL.enter(n)
        // flattening the declarations
        // all declarations with duplicates dropped, and declarations of the same name merged
        var declsF: List[Declaration] = Nil
        def append(d: Declaration, alsoCheck: Boolean) = {
          declsF = declsF ::: List(d)
          if (alsoCheck) envL = checkDeclaration(envL, d)
        }
        def doOne(d: Declaration, alsoCheck: Boolean) = {
          if (!declsF.contains(d))
            d match {
              case nd: NamedDeclaration =>
                declsF.find(_.nameO contains nd.name) match {
                  case None => append(d, alsoCheck)
                  case Some(existing) =>
                    val dM = Declaration.merge(existing,nd)
                    if (dM != existing) {
                      // TODO type-check merged declaration
                      declsF = declsF.filterNot(_ == existing)
                      if (alsoCheck) envL = envL.update(envL.parent, d, dM) // declarations must exist in environment during checking
                      append(dM, alsoCheck)
                    }
                }
              case _ => append(d, alsoCheck)
            }
        }
        // collect, merge, and prepend all inherited declarations
        supsClasses.foreach {case (_,supClass) =>
          supClass.decls.foreach{d => doOne(d, false)}
        }
        val cd2 = cd1.copy(decls = declsF:::ds)
        envL = envL.update(env.parent, cd1, cd2)
        ds.foreach {d => doOne(d, true)}
        envL.leave
      case Include(dom, dfO, realize) =>
        val domC = checkTheory(env, dom)
        val dfOC = dfO map {d => checkExpression(env, d, domC)}
        if (realize) {
          // TODO
        }
        Include(domC, dfOC, realize)
      case sd @ SymDecl(_, tp, dfO) =>
        val (tpC, dfOC) = if (tp == null) dfO match {
          case None => throw Error(sd, "untyped declaration")
          case Some(df) =>
            val (dfC, dfI) = inferExpression(env, df)
            (dfI, Some(dfC))
        } else {
          val tpC = checkType(env, tp)
          val dfOC = dfO map {df =>
            checkExpression(env, df, tp)
          }
          (tpC, dfOC)
        }
        val sdC = sd.copy(tp = tpC, dfO = dfOC)
        // TODO check purity of definiens
        env.update(env.parent, sd, sdC)
      case td@TypeDecl(_,dfO) =>
        val dfOC = dfO map {t => checkType(env,t)}
        val tdC = td.copy(dfO = dfOC)
        env.update(env.parent, td, tdC)
    }
  }

  def checkTheory(env: StaticEnvironment, thy: Theory)(implicit loc: SyntaxFragment): Theory = {
    val partsF = flatten(env, Nil, List(thy.parts))
    Theory(partsF)
  }

  def checkContext(env: StaticEnvironment,c: Context,allowDefinitions: Boolean,allowMutable: Boolean): (StaticEnvironment,Context) = {
    var envL = env
    val declsC = c.decls.map {vd =>
      val vdC = checkVarDecl(envL,vd,allowDefinitions,allowMutable)
      envL = envL.add(vdC)
      vdC
    }
    (envL,Context(declsC))
  }

  def checkVarDecl(env: StaticEnvironment,vd: VarDecl,allowDefinitions: Boolean,allowMutable: Boolean): VarDecl = {
    if (vd.mutable && !allowMutable) throw Error(vd,"mutable variable not allowed here")
    if (vd.value.isDefined && !allowDefinitions) throw Error(vd,"defined variable not allowed here")
    if (vd.tp == null) {
      vd.value match {
        case Some(v) =>
          val (dfC,dfI) = inferExpression(env,v)
          VarDecl(vd.name,dfI, Some(dfC),vd.mutable)
        case None => throw Error(vd, "untyped variable")
      }
    } else {
      val tpC = checkType(env,vd.tp)
      val dfC = vd.value map {d => checkExpression(env,d,vd.tp)}
      VarDecl(vd.name,tpC,dfC,vd.mutable)
    }
  }

  // ***************** Types **************************************
  def checkType(env: StaticEnvironment,tp: Type): Type = keepRef(tp) {
    case TypeRef(p) =>
      env.voc.lookupRelativePath(env.parent, p) match {
        case Some((pC,pd)) =>
          pd match {
            case _: TypeDecl => TypeRef(pC)
            case m: Module =>
              // indeterminate use of module as type interpreted as class type
              if (m.open) throw Error(tp, "open module not a type")
              val pF = flatten(env, Theory(List(pC)))(tp)
              ClassType(pF)
            case _ => throw Error(tp,"not a type symbol")
          }
        case None =>
          throw Error(tp,"symbol not declared")
      }
    case _: BaseType => tp
    case tp: TypeOperator =>
      tp.children.foreach(c => checkType(env,c))
      tp
    case ClassType(thy) =>
      val thyC = checkTheory(env, thy)(tp)
      ClassType(thyC)
    case ExprsOver(thy, q) =>
      val thyC = checkTheory(env, thy)(tp)
      val envQ = env.push(thy)
      val qC = checkType(envQ, q)
      ExprsOver(thyC, qC)
  }


  /** closure under inheritance, in depth-first order
    * invariant: closure(result:::ps.flatten) is unchanged by recursion; result is closed
    * ps:List[Path] would suffice; but ps:List[List[Path]] allows constant-time prepending
    */
  private def flatten(env: StaticEnvironment, result: List[Path], ps: List[List[Path]])(implicit loc: SyntaxFragment): List[Path] = {
    ps match {
      case Nil => result.reverse
      case Nil::tl => flatten(env, result, tl)
      case (hd::tl)::tls =>
        if (result contains hd)
          flatten(env, result, tl::tls)
        else {
          env.voc.lookupRelativePath(env.parent, hd) match {
            case Some((hdC, md: Module)) => flatten(env, hdC::result, md.supers::tl::tls)
            case Some(_) => throw Error(loc, s"$hd not a class")
            case None => throw Error(loc, s"$hd undefined")
          }
        }
    }
  }
  /** closure under inheritance for theories */
  def flatten(env: StaticEnvironment, thy: Theory)(implicit loc: SyntaxFragment): Theory = {
    if (thy.isFlat) return thy // optimization to avoid repeated flattening
    val partsF = flatten(env, Nil, List(thy.parts))
    val thyF = Theory(partsF)
    thyF.isFlat = true
    thyF
  }

  /** sub subtype of sup */
  def checkSubtype(env: StaticEnvironment,sub: Type,sup: Type)(implicit loc: Expression): Unit = {
    val union = typeUnion(env,sub,sup)
    if (union != sup) // Theory overrides equals
      throw Error(loc,s"inferred: $sub; expected: $sup")
  }

  /** flattened if the inputs are */
  def typeUnion(env: StaticEnvironment,tps: List[Type])(implicit loc: Expression): Type = {
    var res: Type = EmptyType
    tps.foreach {tp => res = typeUnion(env,res,tp)}
    res
  }

  /** least common supertype
    * flattened if the inputs are
    */
  def typeUnion(env: StaticEnvironment,a: Type,b: Type)(implicit loc: Expression): Type = {
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
        // aT-expression of type u or bT-expression of type v, i.e., expression over union of union type
        ExprsOver(theoryUnion(env,aT,bT), typeUnion(env, u, v))
      case (ClassType(aT), ClassType(bT)) =>
        // model of aT or model of bT, i.e., model of intersection
        val i = theoryIntersection(env,aT,bT)
        if (i.parts.isEmpty) AnyType else ClassType(i)
      case _ => AnyType
    }
  }

  /** greatest common subtype
    * flattened if the inputs are
    */
  def typeIntersection(env: StaticEnvironment, a: Type, b: Type)(implicit loc: Expression): Type = {
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
        ExprsOver(theoryIntersection(env,aT,bT), typeIntersection(env, u, v))
      case (ClassType(aT), ClassType(bT)) =>
        // model of aT and of bT, i.e., model of the union
        ClassType(theoryUnion(env,aT,bT))
      case _ => EmptyType
    }
  }

  /** union (colimit) of theories */
  def theoryUnion(env: StaticEnvironment, a: Theory, b: Theory): Theory = {
    val pqs = (a.parts ::: b.parts).distinct
    val thy = Theory(pqs)
    thy.isFlat = a.isFlat && b.isFlat // flat if the inputs are
    thy
  }

  /** intersection of theories: the union of all common includes */
  def theoryIntersection(env: StaticEnvironment, a: Theory, b: Theory): Theory = {
    val pqs = a.parts intersect b.parts
    val thy = Theory(pqs)
    thy.isFlat = a.isFlat && b.isFlat // flat if the inputs are
    thy
  }

  /** a included into b */
  def isSubtheory(a: Theory, b: Theory) = {
    a.parts.forall(p => b.parts.contains(p))
  }

  /** definitions expanded, but not flattened */
  def typeNormalize(env: StaticEnvironment, tp: Type): Type = {
    def n(t: Type) = typeNormalize(env, t)
    def f(t: Theory) = flatten(env, t)(tp)
    keepRef(tp) {
      case TypeRef(p) => env.voc.lookupPath(p) match {
        case Some(td: TypeDecl) => td.dfO match {
          case Some(df) => typeNormalize(env, df)
          case None => tp
        }
        case _ => tp
      }
      case _: BaseType => tp
      case FunType(as,a) => FunType(as map n, n(a))
      case ProdType(as) => ProdType(as map n)
      case ListType(a) => ListType(n(a))
      case ClassType(sc) => ClassType(f(sc))
      case ExprsOver(sc, t) => ExprsOver(f(sc), n(t))
      case null =>
        null // should be impossible, only for debugging
    }
  }

  // ***************** Expressions **************************************
  def checkExpression(env: StaticEnvironment,exp: Expression,tp: Type): Expression = {
    implicit val loc = exp
    val tpN = typeNormalize(env, tp)
    val eC = (exp,tpN) match {
      case (ListValue(es),ListType(t)) =>
        val esC = es.map(e => checkExpression(env,e,t))
        ListValue(esC)
      case (Tuple(es),ProdType(ts)) =>
        if (es.length != ts.length) throw Error(exp,"wrong number of components in tuple")
        val esC = (es zip ts) map {case (e,t) => checkExpression(env,e,t)}
        Tuple(esC)
      case (Lambda(ins,out),FunType(inTps,outTp)) =>
        if (ins.decls.length != inTps.length) throw Error(exp,"wrong number of variables in lambda")
        val insT = (ins.decls zip inTps).map {case (invd,intp) =>
          if (invd.tp == null) {
            invd.copy(tp = intp)
          } else {
            checkSubtype(env, intp, invd.tp)
            invd
          }
        }
        val (envL,insC) = checkContext(env,Context(insT),false,false)
        val outC = checkExpression(envL,out,outTp)
        Lambda(insC,outC)
      case (ExprOver(scE,e), ExprsOver(scT, tp)) =>
        val scTC = checkTheory(env, scT)
        if (scE != null) {
          if (!isSubtheory(scE, scTC)) throw Error(exp, "quoted theory not incuded into expected type")
        }
        val envL = env.push(scTC)
        val eC = checkExpression(envL, e, tp)
        ExprOver(scTC, eC)
      case (Application(op: BaseOperator,args),_) if op.tp == null =>
        val (argsC,argsI) = args.map(a => inferExpression(env,a)).unzip
        val opTp = FunType(argsI,tpN)
        val opC = checkExpression(env,op,opTp)
        Application(opC,argsC)
      case (BaseOperator(op,opTp),FunType(ins,out)) =>
        if (opTp != null) {
          checkSubtype(env,opTp,tpN)
        }
        val outI = inferOperator(env, op, ins)
        checkSubtype(env,e,outI,out)
        BaseOperator(op,tpN)
      case _ =>
        val (eC,eI) = inferExpression(env,e)
        checkSubtype(env,eI,tpN)
        eC
    }
    eC.loc = e.loc
    eC
  }

  def inferExpressionNorm(env: StaticEnvironment,e: Expression): (Expression,Type) = {
    val (eC,eI) = inferExpression(env, e)
    (eC, typeNormalize(env,eI))
  }

  def inferExpression(env: StaticEnvironment,exp: Expression): (Expression,Type) = {
    val (expC,expI) = exp match {
      case e: BaseValue => (e,e.tp)
      case op: BaseOperator =>
        if (op.tp == null)
          throw Error(exp, "cannot infer type of operator")
        val ft = typeNormalize(env,op.tp) match {
          case ft:FunType => ft
          case _ => throw Error(exp, "operator type not a function")
        }
        val out = inferOperator(env, exp, op.operator, ft.ins)
        checkSubtype(env, out, ft.out)(exp)
        (BaseOperator(op.operator, ft), op.tp)
      case SymbolRef(p) =>
        val (pC,pd) = env.voc.lookupRelativePath(env.parent, p) getOrElse {
          env.voc.lookupRelativePath(env.parent, p)//DELETE
          throw Error(exp, s"$p is not defined")
        }
        val eI = pd match {
          case fd: SymDecl => fd.tp
          case _ => throw Error(e,s"$p is not an expression")
        }
        (SymbolRef(pC),eI)
      case FieldRef(owner, f) =>
        val (oC,oI) = inferExpression(env,owner)
        val fd = oI match {
          case TypeRef(p) =>
            env.voc.lookupClass(p, Error(exp,"type of owner must be a class"))
          case _ =>
        }
        val eI = fd match {
          case None => throw Error(exp,s"$f not defined")
          case Some(fd: SymDecl) => fd.tp
          case Some(_) => throw Error(exp,s"$f is not an expression")
        }
        val eC = FieldRef(oC,f)
        (eC,eI)
      case VarRef(n) =>
        (exp, env.ctx.lookup(n).tp)
      case ExprOver(t,q) =>
        val tC = checkTheory(env, t)
        val envL = env.push(tC)
        val (qC,qI) = inferExpression(envL, q)
        val vC = envL.voc
        (ExprOver(tC,qC), ExprsOver(tC, qI))
      case Eval(e) =>
        if (env.scopes.isEmpty) throw Error(exp, "eval outside quotation")
        val envL = env.pop()
        val (eC,eI) = inferExpressionNorm(envL, e)
        eI match {
          case ExprsOver(eT, q) =>
            if (!isSubtheory(eT,env.theory)) {
              throw Error(exp, "quoted over wrong theory")
            }
            (Eval(eC),q)
        }
      case Lambda(ins,bd) =>
        val (envL,insC) = checkContext(env,ins,false,false)
        val inTypes = insC.decls.map(_.tp)
        val (bdC,bdI) = inferExpression(envL,bd)
        (Lambda(insC,bdC),FunType(inTypes,bdI))
      case Application(f,as) =>
        f match {
          case op: BaseOperator if op.tp == null =>
            // for an operator of unknown type, we need to infer the argument types first
            val (asC,asI) = as.map(a => inferExpression(env,a)).unzip
            val out = inferOperator(env,e,op.operator,asI)
            val opC = op.copy(tp = FunType(asI,out))
            (Application(opC,asC),out)
          case f =>
            val (fC,fI) = inferExpressionNorm(env,f)
            fI match {
              case FunType(ins,out) =>
                if (as.length != ins.length) throw Error(e,"wrong number of arguments")
                val asC = (as zip ins).map {case (a,i) => checkExpression(env,a,i)}
                (Application(fC,asC),out)
              case _ => throw Error(f,"not a function")
            }
        }
      case Tuple(es) =>
        val (esC,esI) = es.map(e => inferExpression(env,e)).unzip
        (Tuple(esC),ProdType(esI))
      case Projection(tup, p) =>
        val (tupC,tupI) = inferExpressionNorm(env,tup)
        tupI match {
          case ProdType(ts) =>
            if (p <= 0) throw Error(e, "non-positive index")
            if (p > ts.length) throw Error(e, "index out of bounds")
            (Projection(tupC,p), ts(p))
          case _ => throw Error(e, "not a list")
        }
      case ListValue(es) =>
        val (esC,esI) = es.map(e => inferExpression(env,e)).unzip
        val eI = typeUnion(env,esI)
        (ListValue(esC),ListType(eI))
      case ListElem(l, p) =>
        val (lC,lI) = inferExpressionNorm(env, l)
        val pC = checkExpression(env, l, IntType)
        lI match {
          case ListType(t) =>
            // list index bound unchecked
            (ListElem(lC,pC), t)
          case _ => throw Error(e, "not a list")
        }
      case Block(es) =>
        var envL = env // local environment, includes variables seen in the block so far
        var eTp: Type = UnitType // type of the last seen expression in the block
        val esC = es.map {e =>
          val (eC,eI) = inferExpression(envL, e)
          eTp = eI
          eC match {
            case vd:VarDecl =>
              val vdNoDef = if (vd.value.isDefined && vd.mutable) vd.copy(value = None) else vd
              envL = envL.add(vdNoDef)
            case _ =>
          }
          eC
        }
        (Block(esC), eTp)
      case VarDecl(n, tp, vlO, mut) =>
        val (tpC,vlC) = if (tp == null) {
          vlO match {
            case None => throw Error(e, "untyped variables")
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
        val (eC,_) = inferExpression(env, e)
        eC match {
          case VarRef(n) =>
            val vd = env.ctx.lookup(n)
            if (!vd.mutable) throw Error(e,"variable not mutable")
            val dfC = checkExpression(env,df,vd.tp)
            (Assign(eC,dfC),UnitType)
          case _ => throw Error(e,"expression not assignable")
        }
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
            if (u == AnyType) throw Error(e, "branches have incompatible types")
            (Some(elsC), u)
          case None => (None,UnitType)
        }
        (IfThenElse(condC, thnC, elsOC), eI)
      case For(n, range, bd) =>
        val (rangeC,rangeI) = inferExpressionNorm(env, range)
        val nTp = rangeI match {
          case ListType(t) => t
          case _ => throw Error(e, "not iterable")
        }
        val bdC = checkExpression(env.add(VarDecl(n,nTp)), bd, AnyType)
        (For(n, rangeC, bdC), UnitType)
    }
    expC.loc = exp.loc
    (expC,expI)
  }

  def inferOperator(env: StaticEnvironment, e: Expression,op: Operator,ins: List[Type]): Type = {
    if (ins.isEmpty) throw Error(e,"operator needs arguments")
    op match {
      case p: PrefixOperator =>
        if (ins.length != 1) throw Error(e, "wrong number of arguments")
        (p, ins.head) match {
          case (UMinus, s@(IntType|RatType)) => s
          case (Not, BoolType) => BoolType
          case _ => throw Error(e, "ill-typed arguments")
        }
      case inf: InfixOperator =>
        if (ins.length != 2) throw Error(e, "wrong number of arguments")
        (inf, ins(0), ins(1)) match {
          case (Divide, IntType, IntType) => RatType
          case (_: Arithmetic, s@(IntType|RatType), t@(IntType|RatType)) => typeUnion(env, s,t)
          case (Plus, StringType, StringType) => StringType
          case (Plus, ListType(s), ListType(t)) if s == t =>
            val u = typeUnion(env,s,t)
            if (u == AnyType) Error(e, "incompatible lists")
            ListType(u)
          case (_:Connective, BoolType, BoolType) => BoolType
          case (_:Comparison, s@(IntType|RatType|BoolType|StringType), t@(IntType|RatType|BoolType|StringType)) if s == t => BoolType
          case (_:Equality, s, t)  =>
            val u = typeUnion(env, s, t)
            if (u == AnyType) throw Error(e, "comparison of incompatible types")
            BoolType
          case _ => throw Error(e, "ill-typed operator")
        }
    }
  }
}
