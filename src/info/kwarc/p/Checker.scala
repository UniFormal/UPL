package info.kwarc.p

import SyntaxFragment.matchC

object Checker {
  case class Error(cause: SyntaxFragment,msg: String) extends PError(cause.loc + ": " + msg + " while checking " + cause.toString)
  def fail(m: String)(implicit cause: SyntaxFragment) = throw Error(cause,m)

  def checkProgram(p: Program): Program = matchC(p) {
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
    implicit val cause = decl
    decl match {
      case nd: NestingDeclaration[_] =>
        nd.decls.groupBy(_.nameO).foreach {case (n,ds) =>
          if (n.isDefined && ds.length > 1) {
            fail("name already defined: " + n.get)
          }
        }
      case _ =>
    }
    decl match {
      case Vocabulary(ds) =>
        if (env.parent.isRoot)
          checkDeclarations(env, ds)
        else
          fail("vocabulary not allowed as nested declaration")
      case m:Module =>
        // invariant: m.supers is the flattening of all includes that have been checked already
        //   m.supers is extended after checking an include
        if (m.closed) {
          m.supers = Theory(Nil)
          m.realizes = Nil
          m.flat = Nil
        }
        val envC = checkDeclarations(env.enter(m.name), m.decls).leave
        if (m.closed) {
          // full flattening
          var result : List[SymbolDeclaration] = Nil
          var todo: List[List[Declaration]] = List(m.decls)
          while (!todo.isEmpty) {
            todo.head match {
              case Nil => todo = todo.tail
              case d :: ds => d match {
                case sd: SymbolDeclaration =>
                  result.find(_.nameO contains sd.name) match {
                    case None => result ::= sd
                    case Some(oldSd) =>
                      if (oldSd != sd) {
                        val m = merge(envC,oldSd, sd)
                        result ::= m
                        oldSd.redundant = true
                      }
                  }
                case id: Include =>
                  id.dom.parts.reverseMap {i =>
                    val im = env.voc.lookupModule(i.path).getOrElse(fail("unknown module")(id))
                    if (i.path == envC.parent) fail("module includes itself")(id)
                    todo ::= im.decls
                  }
                case _ => // TODO ?
              }
            }
          }
          // return 'result' after reversing and filtering out redundant declarations
          var flat: List[SymbolDeclaration] = Nil
          result.foreach {d => if (!d.redundant) flat ::= d}
          m.flat = flat
          val defined = flat collect {
            case sd if sd.dfO.isDefined => sd.name
          }
          m.realizes.foreach {p =>
            val needed = env.voc.lookupModule(p).get.flat.collect {
              case sd if sd.dfO.isEmpty => sd.name
            }
            val missing = needed.filterNot(defined.contains(_))
            if (missing.nonEmpty) fail(s"realization of $p not total: ${missing.mkString(", ")}")(m)
          }
          // TODO instance creation may occur before or while a theory is checked - needs 2-phase approach
        }
        envC
      case id@Include(dom, dfO) =>
        val mod = env.parentDecl match {
          case Some(m: Module) if m.closed => m
          case _ => fail("include only allowed in closed module")
        }
        val idC = if (dom != null) {
          val domC = checkTheory(env, dom)(id)
          val dfOC = if (dfO contains null) None else dfO map {d => checkExpression(env,d,ClassType(domC))}
          Include(domC,dfOC)
        } else dfO match {
          case None => fail("untyped include")
          case Some(df) =>
            // infer domain from definiens
            val (dfC,dfI) = inferExpression(env,df)
            dfI match {
              case ClassType(thy) =>
                Include(thy, Some(dfC))
              case _ => fail("domain not a theory")
            }
        }
        mod.supers = relativeFlatten(env, mod.supers, idC.dom)(id)
        if (id.realize) mod.realizes :::= id.dom.parts.collect {case i if i.dfO.isEmpty => i.path}
        env.update(env.parent, id, idC)
      case sd: SymbolDeclaration =>
        val thy = env.parentDecl match {
          case Some(m: Module) if m.closed => m.supers
          case _ => Theory(Nil)
        }
        val sdC = checkSymDeclAgainstTheory(env, thy, sd)
        // TODO check purity of definiens
        env.update(env.parent, sd, sdC)
    }
  }

  // TODO does not check compatibility
  def checkTheory(env: StaticEnvironment, thy: Theory)(implicit cause: SyntaxFragment): Theory = {
    val inclsC = thy.parts.map {i =>
      val pC = env.voc.lookupRelativePath(env.parent, i.path) match {
        case Some((q,m:Module)) => q
        case Some(_) => fail("not a module")
        case None => fail("undefined module")
      }
      val dfOC = i.dfO map {d => checkExpression(env, d, ClassType(Theory(pC)))}
      Inclusion(pC, dfOC)
    }
    val partsF = flatten(env, Nil, List(inclsC))
    Theory(partsF)
  }

  /** thy: a theory that possibly provides the expected type, sd: the declaration to check
    * cases:
    * - type: type of sd may be Present/Omitted
    * - definition: sd may be Undefined/Defined
    * - inherited: theory may have No/Other/Abstract/Concrete declaration for the name
    */
  def checkSymDeclAgainstTheory(env: StaticEnvironment, thy: Theory, sd: SymbolDeclaration): SymbolDeclaration = {
    implicit val cause = sd
    lookupInTheory(env,thy,sd.name) match {
      // switch on inherited
      case Some((_,abs: SymbolDeclaration)) =>
        if (abs.kind != sd.kind) fail("name is inherited but has kind " + abs.kind)
        // Concrete: error
        if (abs.dfO.isDefined) fail("name is inherited and already defined")
        // Abstract: inherit type
        val expectedTp = abs.tp
        val tpC = if (sd.tp == null) {
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
            val tpC = if (td.tp == null) AnyType else checkType(env,td.tp)
            val dfOC = td.dfO map {df => checkType(env,df,tpC)}
            td.copy(tp = tpC,dfO = dfOC)
          case sd: ExprDecl =>
            val (tpC,dfC) = if (sd.tp == null) {
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
    implicit val cause = vd
    if (vd.mutable && !allowMutable) fail("mutable variable not allowed here")
    if (vd.value.isDefined && !allowDefinitions) fail("defined variable not allowed here")
    if (vd.tp == null) {
      vd.value match {
        case Some(v) =>
          val (dfC,dfI) = inferExpression(env,v)
          VarDecl(vd.name,dfI, Some(dfC),vd.mutable)
        case None => fail("untyped variable")
      }
    } else {
      val tpC = checkType(env,vd.tp)
      val dfC = vd.value map {d => checkExpression(env,d,vd.tp)}
      VarDecl(vd.name,tpC,dfC,vd.mutable)
    }
  }

  // ***************** Types **************************************
  def checkType(env: StaticEnvironment,tp: Type, bound: Type): Type = {
    val tpC = checkType(env,tp)
    checkSubtype(env, tp, bound)(tp)
    tpC
  }
  def checkType(env: StaticEnvironment,tp: Type): Type = {
    implicit val cause = tp
    matchC(tp) {
      case TypeRef(p) =>
        resolveName(env, p) match {
          case Some(NameResolution(pC,pd: TypeDecl,closed)) =>
            if (closed) TypeFieldRef(None,p.head) else TypeRef(pC)
          case Some(NameResolution(pC, m: Module, false)) =>
            // TODO: what if m is defined inside the class
            // indeterminate use of module as type interpreted as class type
            if (!m.closed) fail("open module not a type")
            val pF = flatten(env,Theory(pC))(tp)
            ClassType(pF)
          case Some(_) => fail(s"$p is not a type")
          case None => fail(s"$p is not defined")
        }
      case TypeFieldRef(ownerO,f) =>
        resolveField(env, ownerO, f) match {
          case (oC,td:TypeDecl) =>
            oC foreach {o =>
              val pure = isPure(env, o)
              if (!pure) fail("impure owner of type field")
            }
            TypeFieldRef(oC,f)
          case _ => fail("not a type")
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
  }


  /** closure under inheritance, in depth-first order
    * invariant: closure(result:::ps.flatten) is unchanged by recursion; result is closed
    * ps:List[_] would suffice; but ps:List[List[_]] allows constant-time prepending
    */
  private def flatten(env: StaticEnvironment, result: List[Inclusion], ps: List[List[Inclusion]])
                     (implicit cause: SyntaxFragment): List[Inclusion] = {
    ps match {
      case Nil => result.filterNot(_.redundant).reverse
      case Nil::tl => flatten(env, result, tl)
      case (hd::tl)::tls =>
        result.find(_.path == hd.path) match {
          case Some(i) =>
            // include of hd.path already exists
            val resultH = if (i.dfO == hd.dfO || hd.dfO.isEmpty) {
              // redundant: drop hd
              result
            } else if (i.dfO.isEmpty) {
              // no definiens so far: add hd, remove old include later
              i.redundant = true
              hd::result
            } else {
              // TODO: check equality, then drop
              fail("conflicting definitions")
            }
            flatten(env,resultH,tl :: tls)
          case None =>
            // new include, add it and recurse into its supers
            env.voc.lookupPath(hd.path) match {
              case Some(md: Module) =>
                val incls = md.decls collect {
                  case i: Include => i.dom.parts.map(_.compose(hd))
                }
                flatten(env, hd::result, incls:::tl::tls)
              case Some(_) => fail(s"${hd.path} not a class")
              case None => fail(s"${hd.path} undefined")
            }
        }
    }
  }
  /** closure under inheritance for theories */
  def flatten(env: StaticEnvironment, thy: Theory)(implicit cause: SyntaxFragment): Theory = {
    if (thy.isFlat) return thy // optimization to avoid repeated flattening
    val partsF = flatten(env, Nil, List(thy.parts))
    val thyF = Theory(partsF)
    thyF.isFlat = true
    thyF
  }
  /** unite a flat theory and another one without reflattening the former */
  def relativeFlatten(env: StaticEnvironment, flatThy: Theory, other: Theory)(implicit cause: SyntaxFragment): Theory = {
    val union = Theory(flatten(env, flatThy.parts, List(other.parts)))
    union.isFlat = true
    union
  }

  /** pre: theory is flat and well-formed
    * multiple declarations of the same name are merged
    */
  def lookupInTheory(env: StaticEnvironment, thy: Theory, n: String): Option[(Path,Declaration)] = {
    var sofar: List[(Path,SymbolDeclaration)] = Nil
    thy.parts.foreach {i =>
      env.voc.lookupPath(i.path/n) foreach {
        case hd: SymbolDeclaration =>
          if (hd.dfO.isDefined || i.dfO.isDefined) {
            // hd has/acquires definiens, so return right away
            val hdL = i.dfO match {
              case Some(own) => OwnerSubstitutor(own,hd)
              case None => hd
            }
            return Some((i.path,hdL))
          } else {
            // hd remains undefined, remember it
            sofar ::= (i.path, hd)
          }
        case _ =>
      }}
    if (sofar.isEmpty) None else {
      var merged = sofar.head._2
      sofar.tail foreach {case (_,d) =>
        merged = merge(env, merged, d)
      }
      Some((sofar.head._1,merged))
    }
  }

  // TODO more compatibility checks needed
  def merge(env: StaticEnvironment, d: SymbolDeclaration, e: SymbolDeclaration): SymbolDeclaration = {
    if (d == e) return d
    implicit val cause = e
    if (d.kind != e.kind) fail("incompatbile kinds")
    if (d.nameO != e.nameO) fail("incompatbile names")
    if (d.dfO.isDefined && e.dfO.isDefined) fail("incompatible definitions")
    val tpM = typeIntersection(env,d.tp,e.tp)
    (d,e) match {
      case (d: ExprDecl,e:ExprDecl) => d.copy(tp = tpM, dfO = d.dfO orElse e.dfO)
      case (d: TypeDecl,e:TypeDecl) => d.copy(tp = tpM, dfO = d.dfO orElse e.dfO)
      case _ => throw Error(d, "impossible case")
    }
  }

  /** sub subtype of sup */
  def checkSubtype(env: StaticEnvironment,sub: Type,sup: Type)(implicit cause: SyntaxFragment): Unit = {
    val union = typeUnion(env,sub,sup)
    if (union != sup) // Theory overrides equals
      fail(s"found: $sub; expected: $sup")
  }

  /** flattened if the inputs are */
  def typeUnion(env: StaticEnvironment,tps: List[Type])(implicit cause: SyntaxFragment): Type = {
    var res: Type = EmptyType
    tps.foreach {tp => res = typeUnion(env,res,tp)}
    res
  }

  /** least common supertype
    * flattened if the inputs are
    */
    //TODO type bounds
  def typeUnion(env: StaticEnvironment,a: Type,b: Type)(implicit cause: SyntaxFragment): Type = {
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
  def typeIntersection(env: StaticEnvironment, a: Type, b: Type)(implicit cause: SyntaxFragment): Type = {
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
  def theoryUnion(env: StaticEnvironment, a: Theory, b: Theory): Theory = {
    val pqs = (a.parts ::: b.parts).distinct //TODO error if definiens do not agree; or if local definitions do not agree
    val thy = Theory(pqs)
    thy.isFlat = a.isFlat && b.isFlat // flat if the inputs are
    thy
  }

  /** intersection of theories: the union of all common includes */
  def theoryIntersection(env: StaticEnvironment, a: Theory, b: Theory): Theory = {
    val pqs = a.parts intersect b.parts // TODO remove definiens if not the same
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
    matchC(tp) {
      case TypeRef(p) => env.voc.lookupPath(p) match {
        case Some(td: TypeDecl) => td.dfO match {
          case Some(df) => n(df)
          case None => tp
        }
        case _ => fail("illegal type")(tp) // impossible if tp is checked
      }
      case TypeFieldRef(ownO, f) =>
        resolveField(env,ownO, f)(tp) match {
          case (oC,td:TypeDecl) => td.dfO match {
            case None => TypeFieldRef(oC,f)
            case Some(df) => oC match {
              case None => n(df)
              case Some(o) =>
                // this code has the effect that type definitions in statically known class types are visible to the outside
                // this is not necessarily desirable
                val os = new OwnerSubstitutor(o)
                n(os.apply(df)(0))
            }
          }
          case _ => fail("illegal type")(tp) // impossible if tp is checked
        }
      case _: BaseType => tp
      case FunType(as,a) => FunType(as map n, n(a))
      case ProdType(as) => ProdType(as map n)
      case ListType(a) => ListType(n(a))
      case OptionType(a) => OptionType(n(a))
      case ClassType(sc) => ClassType(f(sc))
      case ExprsOver(sc, t) => ExprsOver(f(sc), n(t))
      case null =>
        null // should be impossible, only for debugging
    }
  }

  // ***************** Expressions **************************************
  def checkExpression(env: StaticEnvironment,exp: Expression,tp: Type): Expression = {
    implicit val cause = exp
    val tpN = typeNormalize(env, tp)
    val eC = (exp,tpN) match {
      case (ListValue(es),ListType(t)) =>
        val esC = es.map(e => checkExpression(env,e,t))
        ListValue(esC)
      case (Tuple(es),ProdType(ts)) =>
        if (es.length != ts.length) fail("wrong number of components in tuple")
        val esC = (es zip ts) map {case (e,t) => checkExpression(env,e,t)}
        Tuple(esC)
      case (Lambda(ins,out),FunType(inTps,outTp)) =>
        if (ins.decls.length != inTps.length) fail("wrong number of variables in lambda")
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
          if (!isSubtheory(scE, scTC)) fail("quoted theory not incuded into expected type")
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
        checkSubtype(env,outI,out)
        BaseOperator(op,tpN)
      case _ =>
        val (eC,eI) = inferExpression(env,exp)
        checkSubtype(env,eI,tpN)
        eC
    }
    eC.copyFrom(exp)
    eC
  }

  def inferExpressionNorm(env: StaticEnvironment,e: Expression): (Expression,Type) = {
    val (eC,eI) = inferExpression(env, e)
    (eC, typeNormalize(env,eI))
  }

  def inferExpression(env: StaticEnvironment,exp: Expression): (Expression,Type) = {
    implicit val cause = exp
    val mf = new MagicFunctions(env)
    val (expC,expI) = exp match {
      case e: BaseValue => (e,e.tp)
      case op: BaseOperator =>
        if (op.tp == null)
          fail("cannot infer type of operator")
        val ft = typeNormalize(env,op.tp) match {
          case ft: FunType => ft
          case _ => fail("operator type not a function")
        }
        val out = inferOperator(env,op.operator,ft.ins)
        checkSubtype(env,out,ft.out)(exp)
        (BaseOperator(op.operator,ft),op.tp)
      case SymbolRef(p) =>
        resolveName(env, p) match {
          case Some(NameResolution(pC,pd: ExprDecl,closed)) =>
            val expC = if (closed) FieldRef(None,p.head) else SymbolRef(pC)
            (expC,pd.tp)
          case Some(_) => fail(s"$p is not an expression")
          case None => fail(s"$p is not defined")
        }
      case Instance(thy,ds) =>
        val thyC = checkTheory(env,thy)
        var definednames: List[String] = Nil
        val dsC = ds map {
          case ad: AtomicDeclaration if ad.dfO.isEmpty =>
            fail("undefined declaration in instance")(ad)
          case sd: SymbolDeclaration =>
            definednames ::= sd.name
            checkSymDeclAgainstTheory(env,thyC,sd)
          case i: Include =>
            fail("include unsupported")(i)
        }
        thyC.parts.foreach {p =>
          if (p.dfO.isEmpty) {
            val m = env.voc.lookupModule(p.path).getOrElse(fail("not a module"))
            val missing = m.abstractFields.filterNot(definednames.contains(_))
            if (missing.nonEmpty) fail("missing definitions")
          }
        }
        (Instance(thyC,dsC),ClassType(thyC))
      case FieldRef(ownerO,f) =>
        // TODO: mutable fields and fields not initialized by the type must be stored inside the owner
        resolveField(env, ownerO, f) match {
          case (oC,sd:ExprDecl) =>
            val eC = FieldRef(oC,f)
            oC match {
              case None => (eC,sd.tp)
              case Some(o) =>
                val os = new OwnerSubstitutor(o)
                val eI = os.apply(sd.tp)(0)
                if (os.substituted) {
                  val pure = isPure(env,o)
                  if (!pure) fail("type of field contains local type; owner must be pure")
                }
                (eC,eI)
            }
          case _ => fail("not an expression")
        }
      case InstanceWith(e,p) =>
        val (eC,eI) = inferExpressionNorm(env, e)
        eI match {
          case ClassType(thy) =>
            // TODO: this check is not correct; we must check that every dependency of p that's not already in thy is defined
            // interpreter will simply modify the instance
            val pC = env.voc.lookupRelativePath(env.parent, p) match {
              case Some((parp,m:Module)) =>
                if (!m.closed) fail("upcast requires closed module")
                m.decls.foreach {
                  case hd: AtomicDeclaration if hd.dfO.isEmpty => fail("undefined field in upcast")(hd)
                  case _ =>
                }
                parp
              case _ => fail("upcast requires module")
            }
            val thyP = relativeFlatten(env, thy, Theory(pC))
            (InstanceWith(eC,pC), ClassType(thyP))
          case _ => fail("not an instance")
        }
      case VarRef(n) =>
        (exp,env.ctx.lookup(n).tp)
      case ExprOver(t,q) =>
        val tC = checkTheory(env,t)
        val envL = env.push(tC)
        val (qC,qI) = inferExpression(envL,q)
        val vC = envL.voc
        (ExprOver(tC,qC),ExprsOver(tC,qI))
      case Eval(e) =>
        if (env.scopes.isEmpty) fail("eval outside quotation")
        val envL = env.pop()
        val (eC,eI) = inferExpressionNorm(envL,e)
        eI match {
          case ExprsOver(eT,q) =>
            if (!isSubtheory(eT,env.theory)) {
              fail("quoted over wrong theory")
            }
            (Eval(eC),q)
          case mf.evaluation(_,a) =>
            (mf.evaluation.insert(eC, Nil), a)
          case _ => fail("not a quoted expression")
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
            val out = inferOperator(env,op.operator,asI)
            val opC = op.copy(tp = FunType(asI,out))
            (Application(opC,asC),out)
          case f =>
            val (fC,fI) = inferExpressionNorm(env,f)
            val (fM,ins,out) = fI match {
              case FunType(ins,out) => (fC,ins,out)
              case mf.application(_,FunType(ins,out)) => (mf.application.insert(fC,as),ins,out)
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
          case _ => fail("not a list")
        }
      case ListValue(es) =>
        val (esC,esI) = es.map(e => inferExpression(env,e)).unzip
        val eI = typeUnion(env,esI)
        (ListValue(esC),ListType(eI))
      case ListElem(l, p) =>
        val (lC,lI) = inferExpressionNorm(env, l)
        val pC = checkExpression(env, p, IntType)
        lI match {
          case ListType(t) =>
            // list index bound unchecked
            (ListElem(lC,pC), t)
          case mf.listElement(_,FunType(List(IntType),a)) =>
            (mf.listElement.insert(lC, List(pC)), a)
          case _ => fail("not a list")
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
        val (eC,_) = inferExpression(env, e)
        eC match {
          case VarRef(n) =>
            val vd = env.ctx.lookup(n)
            if (!vd.mutable) fail("variable not mutable")(e)
            val dfC = checkExpression(env,df,vd.tp)
            (Assign(eC,dfC),UnitType)
          case _ => fail("expression not assignable")(e)
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
            if (u == AnyType) fail("branches have incompatible types")
            (Some(elsC), u)
          case None => (None,UnitType)
        }
        (IfThenElse(condC, thnC, elsOC), eI)
      case For(n, range, bd) =>
        val (rangeC,rangeI) = inferExpressionNorm(env, range)
        val (rangeM, nTp) = rangeI match {
          case ListType(t) => (rangeC, t)
          case mf.iteration(_,ListType(t)) => (mf.iteration.insert(rangeC, Nil), t)
          case _ => fail("not iterable")
        }
        val bdC = checkExpression(env.add(VarDecl(n,nTp)), bd, AnyType)
        (For(n, rangeM, bdC), UnitType)
    }
    expC.copyFrom(exp)
    (expC,expI)
  }

  // TODO: check purity of expression
  def isPure(env: StaticEnvironment, exp: Expression) = exp match {
    case _:VarRef | _:SymbolRef => true
    case _ => false
  }

  case class NameResolution(path: Path, decl: Declaration, closed: Boolean)
  // TODO: p could be local in an enclosing closed module
  def resolveName(env: StaticEnvironment, p: Path) = {
    val closedField = if (p.names.length == 1) {
      // p might actually be a local field ref in a closed module; if so, change the expression and restart
      env.parentDecl match {
        case Some(m: Module) if m.closed =>
          lookupInTheory(env,m.theory(env.parent),p.head).map {case (p,d) => NameResolution(p,d,true)}
        case _ => None
      }
    } else {
      None
    }
    closedField orElse {
      env.voc.lookupRelativePath(env.parent,p).map {case (p,d) => NameResolution(p,d,false)}
    }
  }
  def resolveField(env: StaticEnvironment, ownerO: Option[Expression], field: String)(implicit cause: SyntaxFragment) = {
    val (oC,thy) = ownerO match {
      case None =>
        val t = env.parentDecl match {
          case Some(m: Module) => m.theory(env.parent)
          case Some(_) => fail("not a class")
          case None => fail("unknown parent")
        }
        (None,t)
      case Some(o) =>
        val (oC,oI) = inferExpression(env,o)
        oI match {
          case ClassType(thy) => (Some(oC),thy)
          case _ => fail("not a class type")
        }
    }
    val (_,d) = lookupInTheory(env,thy,field).getOrElse {
      fail("unknown field")
    }
    (oC,d)
  }
  def inferOperator(env: StaticEnvironment,op: Operator,ins: List[Type])(implicit cause: Expression): Type = {
    if (ins.isEmpty) fail("operator needs arguments")
    op match {
      case p: PrefixOperator =>
        if (ins.length != 1) fail("wrong number of arguments")
        (p, ins.head) match {
          case (UMinus, s@(IntType|RatType)) => s
          case (Not, BoolType) => BoolType
          case _ => fail("ill-typed arguments")
        }
      case inf: InfixOperator =>
        if (ins.length != 2) fail("wrong number of arguments")
        (inf, ins(0), ins(1)) match {
          case (Divide, IntType, IntType) => RatType
          case (_: Arithmetic, s@(IntType|RatType), t@(IntType|RatType)) => typeUnion(env, s,t)
          case (Plus, StringType, StringType) => StringType
          case (Plus, ListType(s), ListType(t)) if s == t =>
            val u = typeUnion(env,s,t)
            if (u == AnyType) fail("incompatible lists")
            ListType(u)
          case (_:Connective, BoolType, BoolType) => BoolType
          case (_:Comparison, s@(IntType|RatType|BoolType|StringType), t@(IntType|RatType|BoolType|StringType)) if s == t => BoolType
          case (_:Equality, s, t)  =>
            val u = typeUnion(env, s, t)
            if (u == AnyType) fail("comparison of incompatible types")
            BoolType
          case _ => fail("ill-typed operator")
        }
    }
  }
}

class MagicFunctions(env: StaticEnvironment) {
  class MagicFunction(name: String) {
    def insert(owner: Expression,args: List[Expression]) = Application(FieldRef(Some(owner),name),args)
    def unapply(tp: Type) = tp match {
      case ClassType(thy) => Checker.lookupInTheory(env,thy,name) match {
        case Some((_,d: ExprDecl)) => Some((thy,d.tp))
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