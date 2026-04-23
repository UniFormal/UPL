package info.kwarc.p.compiler

import info.kwarc.p.{Application, ApproxReal, BaseOperator, BoolValue, Equality, Expression, IfThenElse, NumberValue, Operator, Program, Rat}

object IRGenerator {

  private var counter = 0

  def fresh(): String = {
    counter += 1
    s"%u$counter"
  }

  def generate(p: Program): IRProgram = {
    val (stmts, value) = visitExpression(p.main)

    IRProgram(
      // TODO
      functions = List(),
      main = IRBlock(stmts :+ IRReturn(value))
    )
  }

  private def visitExpression(e: Expression): (List[IRStmt], IROperand) = e match {
    case NumberValue(tp, re, im) =>
      re match {
        // TODO
        case ApproxReal(value) => (Nil, IRConstInt(value.toInt))
        case Rat(enu, deno) => (Nil, IRConstInt(enu.toInt / deno.toInt))
      }

    case BoolValue(b) =>
      (Nil, IRConstInt(if (b) 1 else 0))

    case Equality(positive, tp, a, b) =>
      val (sa, ea) = visitExpression(a)
      val (sb, eb) = visitExpression(b)

      val tmp = IRVar(fresh())
      val cmp = IrCmp(tmp, if (positive) "eq" else "ne", ea, eb)

      val result = IRVar(fresh())
      val zext = IrI1toI32(result, tmp)

      (sa ++ sb ++ List(cmp, zext), result)
    case Application(fun, args) => fun match {
      case bo: BaseOperator =>
        if (bo.operator.isDynamic) {
          //          frame.inNewBlock {
          //            interpretDynamicBoolean(exp)
          //          }
          ???
        } else
          visitExpression(Operator.simplify(bo, args))
    }

    case IfThenElse(cond, thn, Some(els)) =>
      val (condS, ec) = visitExpression(cond)
      val tmp = IRVar(fresh())

      val trncS = IrI32ToI1(tmp, ec)

      // TODO unique labels
      val thnLS = IRLabel("then")
      val elsLS = IRLabel("else")
      val endLS = IRLabel("end")

      val brEndS = IrBranch(endLS)
      val cndBrS = IrCondBranch(tmp, thnLS, elsLS)

      val (thnS, thnO) = visitExpression(thn)
      val (elsS, elsO) = visitExpression(els)

      val result = IRVar(fresh())

      val phi = IrPhi(result, List((thnO, thnLS), (elsO, elsLS)))

      (condS ++ List(trncS, cndBrS, thnLS) ++ thnS ++ List(brEndS, elsLS) ++ elsS ++ List(brEndS, endLS, phi), result)
    case _ =>
      sys.error(s"Unsupported expression ${e.getClass} $e")
  }
}