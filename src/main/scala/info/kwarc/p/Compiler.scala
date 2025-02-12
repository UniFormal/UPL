package info.kwarc.p

/** a compiler to Javascript */
// TODO unfinished
object Compiler {
  case class Error(cause: SyntaxFragment, msg: String) extends SError(cause.loc, msg)

  def compileExpression(exp: Expression, statement: Boolean = false, addReturn: Boolean = false): JS = {
    def c(e: Expression) = compileExpression(e,statement,false)

    def cE(e: Expression) = compileExpression(e,false,false)
    def compileAndPushReturn(e: Expression) = compileExpression(e,statement,addReturn)

    exp match {
      case VarRef(n) => JVarRef(n)
      case vd: VarDecl => JVarDecl(vd.name,c(vd.dfO.get))
      case StringValue(s) => JString(s)
      case IntValue(i) => compileInt(i)
      case RatValue(e,d) => JBinOp("/",compileInt(e),compileInt(d)) // TODO
      case UnitValue => JArray(Nil)
      case BoolValue(b) => JBool(b)
      case BaseOperator(op,tp) =>
        val jop = op.symbol // TODO
        op match {
          case pop: PrefixOperator =>
            JFunction(List("__1"),JReturn(JUnOp(jop,JVarRef("__1"))))
          case inf: InfixOperator =>
            JFunction(List("__1","__2"),JReturn(JBinOp(jop,JVarRef("__1"),JVarRef("__2"))))
        }
      case Lambda(ins,b) =>
        val names = ins.variables.reverse.map(_.name)
        val bC = compileExpression(b, true)
        JFunction(names,bC)
      case Application(f,as) => JApply(c(f),as map c)
      case Tuple(es) => JArray(es map c)
      case Projection(t,i) => JArrayElem(c(t),JInt(i-1))
      case CollectionValue(es) => JArray(es map c)
      case ListElem(l,p) => JArrayElem(c(l),c(p))
      case Block(es) =>
        es match {
          case Nil => JArray(Nil)
          case l =>
            val inits = l.init map c
            val last = compileAndPushReturn(l.last)
            JBlock(inits ::: List(last))
        }
      case IfThenElse(cond,thn,elsO) =>
        val condC = cE(cond)
        elsO match {
          case Some(els) if !statement => JTernary(condC,c(thn),c(els))
          case _ => JIf(condC,compileAndPushReturn(thn),elsO map compileAndPushReturn)
        }
      case While(cond,bd) => JWhile(cE(cond),c(bd))
      case Return(e,thrw) =>
        val eC = cE(e)
        if (thrw) JThrow(eC) else JReturn(eC)
      case Assert(f) =>
        val fC = c(f)
        JIf(JUnOp("!", fC), JThrow(JString("assertion failed")), None)
      case q: Quantifier => throw Error(q,"cannot compile quantifier")
    }
  }
  def compileInt(b: BigInt) = JApply(JVarRef("BigInt"), List(JString(b.toString)))
}
