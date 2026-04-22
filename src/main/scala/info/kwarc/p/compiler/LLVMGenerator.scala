package info.kwarc.p.compiler

class LLVMGenerator {

  private var counter = 0
  def fresh(): String = {
    counter += 1
    s"%v$counter"
  }

  def visitBlock(b: IRBlock): String =
    b.stmts.flatMap(visitStmt).map(s => s"\t$s").mkString("\n")

  private def visitStmt(s: IRStmt): List[String] = s match {
    case IrCmp(result, cond, left, right) =>
      // https://llvm.org/docs/LangRef.html#icmp-instruction
      val origIv = op{result}
      val icmp = s"$origIv = icmp $cond i32 ${op(left)}, ${op(right)}"

      // reassign variable to fresh name, because following instructions should use the extended i32 variable, not i1
      result.name = fresh()
      val zext = s"${op(result)} = zext i1 $origIv to i32"
      List(icmp, zext)

    case IrAdd(result, left, right) =>
      val add = s"${op(result)} = add i32 ${op(left)}, ${op(right)}"
      List(add)

    case IRReturn(v) =>
      val vv = op(v)
      List(s"ret i32 $vv")
  }

  private def op(e: IROperand): String = e match {
    case IRVar(name) => name
    case IRConstInt(value) => value.toString
  }
}