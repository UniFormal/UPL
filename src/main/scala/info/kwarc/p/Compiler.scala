package info.kwarc.p

case class RegionCompilation(theory: Path, instance: JVarRef)

/** a compiler to Javascript */
// TODO unfinished
object Compiler {
  def thisRef(l: Int) = "_this_" + l

  case class Error(cause: SyntaxFragment, msg: String) extends SError(cause.loc, msg)

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
        val regs = (parents zip thises).map {case (p,t) => RegionCompilation(p,JVarRef(t))}
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

  def encodeExpression(exp: Expression): JS = {JObject()} //TODO

  /**
    * @param exp the expression to compile
    * @param thises the variables holding the instances of the surrounding theories
    * @param statement no need to return a value
    * @param addReturn prefix with "return" (unless redundant)
    */
  def compileExpression(exp: Expression, regions: List[RegionCompilation], statement: Boolean, addReturn: Boolean): JS = {
    def c(e: Expression) = compileExpression(e, regions, false, false)
    def compileStatement(e: Expression) = compileExpression(e, regions, true, false)
    def compileAndPushReturn(e: Expression) = compileExpression(e, regions, true, addReturn)

    var returnAdded = false
    val expC = exp match {
      case This(l) => regions(l-1).instance
      case Instance(thy) =>
        val n = "_instance_" + (regions.length+1)
        thy match {
          case ExtendedTheory(p,ds) =>
            val regs = RegionCompilation(p,JVarRef(n)) :: regions
            val dsC = ds.collect {
              case ed: ExprDecl =>
                val dfC = compileExpression(ed.dfO.get,regs, false, false)
                JVarDef(n + "." + ed.name,dfC)
            }
            JBlock(JVarDef(n,JObject()) :: dsC).asExpression()
          case _ => throw Error(exp,"unexpected instance")
        }
      case OwnedExpr(owner,dom,owned) =>
        val ownerName = "_owner_" + (regions.length+1)
        val ownerJ = JVarDef(ownerName, c(owner))
        val path = dom match {
          case ExtendedTheory(p,_) => p
          case _ => throw Error(exp, "unexpected domain")
        }
        // TODO further regions must be picked from dom if dom is an OwnedModule
        val reg = RegionCompilation(path, JVarRef(ownerName))
        val ownedJ = compileExpression(owned, List(reg), statement, addReturn)
        JBlock(List(ownerJ,ownedJ)).asExpression()
      case ClosedRef(n) =>
        val reg = regions.head
        val jField = JObjectElem(reg.instance, n)
        // if this.n is defined, use it; otherwise, call n(owner1, owner2, ...)
        JTernary(jField, jField, JApply(compilePath(reg.theory), regions.map(_.instance)))
      case OpenRef(p) => compilePath(p)
      case VarRef(n) => JVarRef(n)
      case vd: VarDecl => JVarDecl(vd.name,c(vd.dfO.get), false)
      case StringValue(s) => JString(s)
      case IntValue(i) => compileInt(i)
      case RatValue(e,d) => JBinOp("/",compileInt(e),compileInt(d)) // TODO
      case UnitValue => JObject()
      case BoolValue(b) => JBool(b)
      case BaseOperator(op,tp) =>
        val jop = op.symbol // TODO
        op match {
          case pop: PrefixOperator =>
            JFunction(List("__1"),JReturn(JUnOp(jop,JVarRef("__1"))))
          case inf: InfixOperator =>
            JFunction(List("__1","__2"),JReturn(JBinOp(jop,JVarRef("__1"),JVarRef("__2"))))
        }
      case Lambda(ins,b, mr) =>
        val names = ins.variables.reverse.map(_.name)
        val bC = compileExpression(b, regions, true, true)
        val bCR = if (mr) handleReturn(bC) else bC
        JFunction(names,bCR)
      case Application(f,as) => JApply(c(f),as map c)
      case Tuple(es) => JArray(es map c)
      case Projection(t,i) => JArrayElem(c(t),JInt(i-1))
      case CollectionValue(es) => JArray(es map c)
      case ListElem(l,p) => JArrayElem(c(l),c(p))
      case Block(es) => es match {
          case Nil => JObject()
          case l =>
            val inits = l.init map c
            val last = compileAndPushReturn(l.last)
            val b = JBlock(inits ::: List(last))
            if (statement) b else b.asExpression()
      }
      case IfThenElse(cond,thn,elsO) =>
        val condC = c(cond)
        elsO match {
          case Some(els) if !statement => JTernary(condC,c(thn),c(els))
          case _ => JIf(condC,compileAndPushReturn(thn),elsO map compileAndPushReturn)
        }
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
    val handler = JTernary(exn("name").equal(uplReturn),JReturn(exn("value")),JThrow(exn))
    JTry(j,exn.name,handler)
  }
}
