package info.kwarc.p

/** carries information about where to find fields of an instance
  * @param instance if this has the field, use it
  * @param thy otherwise, call this on the instance
  */
case class RegionalCompilationContext(thy: JS, instance: JVarRef)
/** maps every UPL variable to its substitution to be used for compiling references to it */
case class LocalCompilationContext(vars: List[(String,JS)])

/** a compiler to Javascript */
// TODO unfinished
object Compiler {
  def thisRef(l: Int) = "_this_" + l

  case class Error(cause: SyntaxFragment, msg: String) extends SError(cause.loc, msg)

  // variable names generated during compilation
  /** name of the expression current being matched */
  val matcheeVarName = new VarDecl.SpecialVarName("matchee")
  /** name of the instance currently being created */
  val instanceVarName = new VarDecl.SpecialVarName("instance")

  /** references to functions defined in the prefix that is written in native Javascript */
  def UPLField(f: String) = JVarRef("_UPL").objectElem(f)
  def UPLApply(fun: String, args: JS*) = JApply(UPLField(fun),args.toList)

  def compileDeclaration(parents: List[Path], level: Int, decl: Declaration): List[JS] = {
    val path = parents.headOption.getOrElse(Path.empty) / decl.nameO.getOrElse("")
    val jpath = path.names.mkString(".")
    decl match {
      case m:Module =>
        val levelI = if (m.closed) level+1 else level
        val body = m.decls flatMap {d => compileDeclaration(path::parents, levelI, d)}
        JVarDecl(jpath, JObject(), true) :: body
      case ed: ExprDecl =>
        val thises = parents.zipWithIndex.map(x => thisRef(x._2+1))
        val regs = (parents zip thises).map {case (p,t) => RegionalCompilationContext(compilePath(p),JVarRef(t))}
        val dfC = ed.dfO match {
          case Some(df) => compileExpression(df, regs, false, false)
          case None => encodeExpression(ed.toRef)
        }
        val dfCF = JFunction(thises, JReturn.prefix(dfC))
        List(JVarDef(jpath, dfCF))
      case _:Include => Nil
      case _:TypeDecl => Nil
    }
  }

  /** computation in Javascript returns objects only with a unique field identifying the kind, in particular
    * - "instance" for instance creation expressions
    * - as used here for encoded expressions as used in patterns and ExprOver
    */
  def encodeExpression(exp: Expression): JS = {
    exp match {
      case v: BaseValue => JObject("value", v.toString)
      case o: BaseOperator => JObject("operator", o.operator.symbol)
      case VarRef(n) => n match {
        case EvalTraverser.ReplaceVarName(i) => JVarRef(n)
        case _ => JObject("local",  n)
      }
      case ClosedRef(n) => JObject("regional", n)
      case OpenRef(p) => JObject("global", p.toString)
      case Tuple(es) => JObject("tuple" -> JArray(es map encodeExpression :_*))
      case Projection(e,i) => JObject("elim" -> encodeExpression(e), "projection" -> JInt(i))
      case Lambda(ins,bd,_) => JObject(
        "lambda" -> JArray(ins.namesInOrder.map(JString):_*),
        "body" -> encodeExpression(bd)
      )
      case Application(f,args) => JObject("elim" -> encodeExpression(f), "application" -> JArray(args map encodeExpression :_*))
      case CollectionValue(es) => JObject("collection" -> JArray(es map encodeExpression :_*))
      case Quantifier(q,vs,bd) => JObject(
        (if (q) "forall" else "exists") -> JArray(vs.mapDecls(vd => JString(vd.name)):_*),
        "body" -> encodeExpression(bd)
      )
    }
  }

  /**
    * @param exp the expression to compile
    * @param thises the variables holding the instances of the surrounding theories
    * @param statement no need to return a value
    * @param addReturn prefix with "return" (unless redundant)
    */
  def compileExpression(exp: Expression, regions: List[RegionalCompilationContext],
                        statement: Boolean, addReturn: Boolean): JS = {
    def c(e: Expression) = compileExpression(e, regions, false, false)
    def compileStatement(e: Expression) = compileExpression(e, regions, true, false)
    def compileAndPushReturn(e: Expression) = compileExpression(e, regions, true, addReturn)

    var returnAdded = false
    val expC: JS = exp match {
      case This(l) => regions(l-1).instance
      case Instance(thy) =>
        val n = instanceVarName(regions.length+1)
        val tC = thy match {
          case PhysicalTheory(p,_) => compilePath(p)
          case _ => throw Error(thy, "unexpected theory")
        }
        val regs = RegionalCompilationContext(tC,JVarRef(n)) :: regions
        val dsC = thy.decls.collect {
          case ed: ExprDecl =>
            val dfC = compileExpression(ed.dfO.get,regs,false,false)
            JVarDef(n + "." + ed.name,dfC)
          case _: Include |_: Module => throw Error(exp,"unsupported declaration")
        }
        JBlock(JVarDef(n,JObject("instance" -> UPLApply("instanceId"))) :: dsC).asExpression()
      case OwnedExpr(owner,dom,owned) =>
        val ownerName = "_owner_" + (regions.length+1)
        val ownerJ = JVarDef(ownerName, c(owner))
        val path = dom match {
          case PhysicalTheory(p,_) => p
          case _ => throw Error(exp, "unexpected domain")
        }
        // TODO further regions must be picked from dom if dom is an OwnedModule
        val reg = RegionalCompilationContext(compilePath(path), JVarRef(ownerName))
        val ownedJ = compileExpression(owned, List(reg), statement, addReturn)
        JBlock(List(ownerJ,ownedJ)).asExpression()
      case ClosedRef(n) =>
        val reg = regions.head
        val jField = JObjectElem(reg.instance, n)
        // if this.n is defined, use it; otherwise, call n(owner1, owner2, ...)
        JTernary(jField, jField, JApply(reg.thy, regions.map(_.instance)))
      case OpenRef(p) => compilePath(p)
      case VarRef(n) => JVarRef(n)
      case vd: VarDecl => JVarDecl(vd.name,c(vd.dfO.get), false)
      case e: ExprOver =>
        val (ctx,expR) = EvalTraverser.replaceEvals(e)
        val evalsC = ctx.mapDecls(vd => JVarDef(vd.name, c(vd.dfO.get)))
        val eoC = encodeExpression(expR)
        JBlock(evalsC:::List(eoC)).asExpression()
      case _:Eval => throw Error(exp,"unexpected evaluation")
      case StringValue(s) => JString(s)
      case IntValue(i) => compileInt(i)
      case RatValue(e,d) => JBinOp("/",compileInt(e),compileInt(d)) // TODO
      case UnitValue => JObject()
      case BoolValue(b) => JBool(b)
      case bo: BaseOperator => UPLField(bo.operator.symbol) // TODO
      case Lambda(ins,b, mr) =>
        val names = ins.variables.reverse.map(_.name)
        val bC = compileExpression(b, regions, true, true)
        val bCR = if (mr) handleReturn(bC) else bC
        JFunction(names,bCR)
      case Application(f,as) => JApply(c(f),as map c)
      case Tuple(es) => JArray(es map c :_*)
      case Projection(t,i) => JArrayElem(c(t),JInt(i-1))
      case CollectionValue(es) => JArray(es map c :_*)
      case ListElem(l,p) => JArrayElem(c(l),c(p))
      case Block(es) => es match {
        case Nil => JObject()
        case l =>
          val inits = l.init map c
          val last = compileAndPushReturn(l.last)
          val b = JBlock(inits ::: List(last))
          if (statement) b else b.asExpression()
      }
      case Assign(pat,df) =>
        val eN = matcheeVarName.fresh()
        val dfC = JVarDef(eN, c(df))
        val matchResultVar = JVarRef(eN+"_1")
        val tryMatch = JVarDef(matchResultVar.name, UPLApply("match", encodeExpression(pat), dfC.toRef))
        JIf(JUnOp("!",tryMatch), JThrow(JString("match failure")), None)
        pat match {
          // TODO must produce one assignment per target, must return list of statements, currently only supporting trivial case
          case VarRef(n) => JVarDef(n,c(df))
        }
      case Match(e, mcs, hd) =>
        val eN = matcheeVarName.fresh()
        val eC = JVarDef(eN, c(e))
        val mcsC = mcs.zipWithIndex.map {case (mc,i) =>
          val matchResultVar = JVarRef(eN+"_"+i.toString)
          val tryMatchC = JVarDef(matchResultVar.name, UPLApply("match", encodeExpression(mc.pattern), eC.toRef))
          val subs = mc.context.namesInOrder.map(n => (n, matchResultVar.objectElem(n)))
          val matchesC = matchResultVar
          val bodyC = c(mc.body).makeRedex(subs)
          (tryMatchC, matchesC, bodyC)
        }
        val matchFailJ = JThrow(JString("match failure"))
        mcsC.foldRight[JS](matchFailJ) {case ((vd,cond,thn),rest) => JBlock(List(vd, JIf(cond, thn, Some(rest))))}
      case _:MatchCase => throw Error(exp, "match case outside match")
      case IfThenElse(cond,thn,elsO) =>
        val condC = c(cond)
        elsO match {
          case Some(els) if !statement => JTernary(condC,c(thn),c(els))
          case _ => JIf(condC,compileAndPushReturn(thn),elsO map compileAndPushReturn)
        }
      case For(vd, elems, bd) =>
        JForArray(vd.name, c(elems), c(bd))
      case While(cond,bd) =>
        val w = JWhile(c(cond),compileStatement(bd))
        if (statement) w else JBlock(List(w, JObject())).asExpression()
      case Return(e,thrw) =>
        val eC = c(e)
        returnAdded = true
        if (thrw) JThrow(eC) else makeReturn(eC)
      case Assert(f) =>
        val fC = c(f)
        JIf(JUnOp("!", fC), JThrow(JString("assertion failed")), None)
      case q: Quantifier => throw Error(q,"cannot compile quantifier")
    }
    if (addReturn && !returnAdded) makeReturn(expC) else expC
  }
  def compileInt(b: BigInt) = JApply(JVarRef("BigInt"), List(JString(b.toString)))
  def compilePath(p: Path): JS = if (p.isToplevel) JVarRef(p.head) else JObjectElem(compilePath(p.up), p.name)

  /** only some UPL functions may return, so we compile return-handling into exception-throwing */
  private val uplReturn = JString("UPLReturn")
  private def makeReturn(j: JS) = JThrow(JObject("name" -> uplReturn, "value" -> j))
  private def handleReturn(j: JS) = {
    val exn = JVarRef("exn")
    val handler = JTernary(exn.objectElem("name").equal(uplReturn),JReturn(exn.objectElem("value")),JThrow(exn))
    JTry(j,exn.name,handler)
  }
}
