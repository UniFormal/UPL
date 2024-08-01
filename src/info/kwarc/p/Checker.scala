package info.kwarc.p

object Checker {
  case class Error(cause: SyntaxFragment,msg: String) extends PError(msg + " while checking " + cause.toString)

  def checkProgram(p: Program): Program = p match {
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
      case nd: NestingDeclaration =>
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
      case Module(n,ds) =>
        checkDeclarations(env.enter(n), ds).leave
      case cd @ Class(n, sups, ds) =>
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
      case sd @ SymDecl(_, tp, vlO) =>
        val (tpC, vlOC) = if (tp == null) vlO match {
          case None => throw Error(sd, "untyped declaration")
          case Some(vl) =>
            val (vlC, vlI) = inferExpression(env, vl)
            (vlI, Some(vlC))
        } else {
          val tpC = checkType(env, tp)
          val vlOC = vlO map {vl =>
            checkExpression(env, vl, tp)
          }
          (tpC, vlOC)
        }
        val sdC = sd.copy(tp = tpC, value = vlOC)
        env.update(env.parent, sd, sdC)
      case td@TypeDecl(_,dfO) =>
        val dfOC = dfO map {t => checkType(env,t)}
        val tdC = td.copy(df = dfOC)
        env.update(env.parent, td, tdC)
    }
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
    val tpC = checkType(env,vd.tp)
    val dfC = vd.value map {d => checkExpression(env,d,vd.tp)}
    VarDecl(vd.name,tpC,dfC,vd.mutable)
  }

  def checkType(env: StaticEnvironment,tp: Type): Type = tp match {
    case TypeRef(p) =>
      env.lookupRelativePath(env.parent, p) match {
        case Some((pC,pd)) =>
          pd match {
            case _: Class | _: TypeDecl => TypeRef(pC)
            case _ => throw Error(tp,"not a type symbol")
          }
        case None =>
          throw Error(tp,"symbol not declared")
      }
    case _: BaseType => tp
    case tp: TypeOperator =>
      tp.children.foreach(c => checkType(env,c))
      tp
  }

  def checkSubtype(env: StaticEnvironment,e: Expression,sub: Type,sup: Type): Unit = {
    val union = typeUnion(env,sub,sup)
    if (union != sup)
      throw Error(e,s"inferred: $sub; expected: $sup")
  }

  def typeUnion(env: StaticEnvironment,tps: List[Type]): Type = {
    var res: Type = EmptyType
    tps.foreach {tp => res = typeUnion(env,res,tp)}
    res
  }

  def typeUnion(env: StaticEnvironment,a: Type,b: Type): Type = {
    (a,b) match {
      case (a,b) if a == b => a
      case (AnyType,_) => AnyType
      case (_,AnyType) => AnyType
      case (EmptyType,t) => t
      case (t,EmptyType) => t
      case (ListType(a),ListType(b)) => ListType(typeUnion(env,a,b))
      case (ProdType(as),ProdType(bs)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeUnion(env,x,y)}
        ProdType(abs)
      case (FunType(as,o),FunType(bs,p)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeIntersection(env,x,y)}
        val op = typeUnion(env,o,p)
        FunType(abs,op)
      case (r1: TypeRef,r2: TypeRef) =>
        val c1 = env.voc.lookupClass(r1.path, Error(r1, "not a class type"))
        val c2 = env.voc.lookupClass(r2.path, Error(r2, "not a class type"))
        val cs = (r1::c1.supers ::: r2::c2.supers).distinct
        ClassUnion(cs)
      case _ => AnyType
    }
  }

  def typeIntersection(env: StaticEnvironment, a: Type, b: Type): Type = {
    (a,b) match {
      case (a,b) if a == b => a
      case (AnyType,t) => t
      case (t,AnyType) => t
      case (EmptyType,_) => EmptyType
      case (_,EmptyType) => EmptyType
      case (ListType(a),ListType(b)) => ListType(typeIntersection(env,a,b))
      case (ProdType(as),ProdType(bs)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeIntersection(env,x,y)}
        ProdType(abs)
      case (FunType(as,o),FunType(bs,p)) if as.length == bs.length =>
        val abs = (as zip bs).map {case (x,y) => typeUnion(env,x,y)}
        val op = typeIntersection(env,o,p)
        FunType(abs,op)
      case (r1: TypeRef,r2: TypeRef) =>
        val c1 = env.voc.lookupClass(r1.path, Error(r1, "not a class type"))
        val c2 = env.voc.lookupClass(r2.path, Error(r2, "not a class type"))
        val cs = (r1::c1.supers) intersect (r2::c2.supers)
        ClassUnion(cs)
      case _ => EmptyType
    }
  }

  def typeNormalize(env: StaticEnvironment, tp: Type): Type = {
    def n(t: Type) = typeNormalize(env, t)
    tp match {
      case TypeRef(p) => env.voc.lookupPath(p) match {
        case Some(td: TypeDecl) => td.df match {
          case Some(t) => typeNormalize(env, t)
          case None => tp
        }
        case _ => tp
      }
      case _: BaseType => tp
      case FunType(as,a) => FunType(as map n, n(a))
      case ProdType(as) => ProdType(as map n)
      case ListType(a) => ListType(n(a))
    }
  }

  def checkExpression(env: StaticEnvironment,e: Expression,tp: Type): Expression = {
    val tpN = typeNormalize(env, tp)
    (e,tpN) match {
      case (ListValue(es),ListType(t)) =>
        val esC = es.map(e => checkExpression(env,e,t))
        ListValue(esC)
      case (Tuple(es),ProdType(ts)) =>
        if (es.length != ts.length) throw Error(e,"wrong number of components in tuple")
        val esC = (es zip ts) map {case (e,t) => checkExpression(env,e,t)}
        Tuple(esC)
      case (Lambda(ins,out),FunType(inTps,outTp)) =>
        if (ins.decls.length != inTps.length) throw Error(e,"wrong number of variables in lambda")
        // TODO use inTps
        val (envL,insC) = checkContext(env,ins,false,false)
        val outC = checkExpression(envL,out,outTp)
        Lambda(insC,outC)
      case (Application(op: BaseOperator,args),_) if op.tp == null =>
        val (argsC,argsI) = args.map(a => inferExpression(env,a)).unzip
        val opTp = FunType(argsI,tpN)
        val opC = checkExpression(env,op,opTp)
        Application(opC,argsC)
      case (BaseOperator(op,opTp),FunType(ins,out)) =>
        if (opTp != null) {
          checkSubtype(env,e,opTp,tpN)
        }
        val outI = inferOperator(e, op,ins)
        checkSubtype(env,e,outI,out)
        BaseOperator(op,tpN)
      case _ =>
        val (eC,eI) = inferExpression(env,e)
        checkSubtype(env,e,eI,tpN)
        eC
    }
  }

  def inferOperator(e: Expression,op: Operator,ins: List[Type]): Type = {
    if (ins.isEmpty) throw Error(e,"operator needs arguments")
    op match {
      case Plus =>
        if (ins.forall(_ == IntType)) IntType
        else if (ins.forall(_ == StringType)) StringType
        else throw Error(e,"illegal argument types")
    }
  }

  def inferExpressionNorm(env: StaticEnvironment,e: Expression): (Expression,Type) = {
    val (eC,eI) = inferExpression(env, e)
    (eC, typeNormalize(env,eI))
  }

  def inferExpression(env: StaticEnvironment,e: Expression): (Expression,Type) = e match {
    case e: BaseValue => (e,e.tp)
    case op: BaseOperator =>
      if (op.tp == null)
        throw Error(e, "cannot infer type of operator")
      val ft = typeNormalize(env,op.tp) match {
        case ft:FunType => ft
        case _ => throw Error(e, "operator type not a function")
      }
      val out = inferOperator(e, op.operator, ft.ins)
      checkSubtype(env, e, out, ft.out)
      (BaseOperator(op.operator, ft), op.tp)
    case SymbolRef(p) =>
      val (pC,pd) = env.lookupRelativePath(env.parent, p) getOrElse {
        env.lookupRelativePath(env.parent, p)//DELETE
        throw Error(e, s"$p is not defined")
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
          env.voc.lookupClass(p, Error(e,"type of owner must be a class"))
        case _ =>
      }
      val eI = fd match {
        case None => throw Error(e,s"$f not defined")
        case Some(fd: SymDecl) => fd.tp
        case Some(_) => throw Error(e,s"$f is not an expression")
      }
      val eC = FieldRef(oC,f)
      (eC,eI)
    case VarRef(n) =>
      (e, env.ctx.lookup(n).tp)
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
          val out = inferOperator(e,op.operator,asI)
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
          if (p < 0) throw Error(e, "negative index")
          if (p >= ts.length) throw Error(e, "index out of bounds")
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
        e match {
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
          (Some(elsC), typeUnion(env, thnI, elsI))
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
}
