package info.kwarc.p.compiler

class LLVMGenerator {

  def visitBlock(b: IRBlock): String =
    b.stmts.map(formatStmt).mkString("\n")

  private def formatStmt(stmt: IRStmt): String =
    if (stmt.indentation()) s"\t${stmt.toLLVMStmt}"
    else stmt.toLLVMStmt

}