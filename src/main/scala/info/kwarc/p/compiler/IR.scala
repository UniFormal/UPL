package info.kwarc.p.compiler

sealed trait IR

case class IRProgram(
                      functions: List[IRFun],
                      main: IRBlock
                    ) extends IR

case class IRFun(
                  name: String,
                  params: List[String],
                  body: IRBlock
                ) extends IR

case class IRBlock(stmts: List[IRStmt]) extends IR

sealed trait IRStmt extends IR

case class IRReturn(value: IROperand) extends IRStmt
case class IrCmp(result: IRVar, cond: String, left: IROperand, right: IROperand) extends IRStmt
case class IrAdd(result: IRVar, left: IROperand, right: IROperand) extends IRStmt


sealed trait IROperand extends IR

case class IRVar(var name: String) extends IROperand
case class IRConstInt(value: Int) extends IROperand