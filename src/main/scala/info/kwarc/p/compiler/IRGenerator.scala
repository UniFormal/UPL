package info.kwarc.p.compiler

import info.kwarc.p.{Application, ApproxReal, BaseOperator, BoolValue, Equality, Expression, NumberValue, Operator, Program, Rat}

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
    case NumberValue(tp, re, im) => {
      re match {
        // TODO
        case ApproxReal(value) => (Nil, IRConstInt(value.toInt))
        case Rat(enu, deno) => (Nil, IRConstInt(enu.toInt / deno.toInt))
      }
    }

    case BoolValue(b) =>
      (Nil, IRConstInt(if (b) 1 else 0))

    case Equality(positive, tp, a, b) => {
      val (sa, ea) = visitExpression(a)
      val (sb, eb) = visitExpression(b)

      val result = IRVar(fresh())

      val s = IrCmp(result, if (positive) "eq" else "ne", ea, eb)

      (sa ++ sb ++ Seq(s), result)
    }
    case Application(f, args) => f match {
      case bo:BaseOperator =>
        if (bo.operator.isDynamic) {
//          frame.inNewBlock {
//            interpretDynamicBoolean(exp)
//          }
          ???
        } else
          visitExpression(Operator.simplify(bo, args))
    }


    case _ =>
      sys.error(s"Unsupported expression ${e.getClass} $e")
  }
}