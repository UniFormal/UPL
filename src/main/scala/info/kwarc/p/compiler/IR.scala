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

sealed trait IRStmt extends IR {
  def indentation() = true

  def toLLVMStmt: String
}

case class IRReturn(value: IROperand) extends IRStmt {
  override def toLLVMStmt = s"ret i32 $value"
}

case class IRLabel(value: String) extends IRStmt {
  override def indentation() = false

  override def toLLVMStmt = s"$value:"
}

case class IrCmp(result: IRVar, cond: String, left: IROperand, right: IROperand) extends IRStmt {
  override def toLLVMStmt = s"$result = icmp $cond i32 $left, $right"
}

case class IrI1toI32(result: IRVar, value: IROperand) extends IRStmt {
  override def toLLVMStmt = s"$result = zext i1 $value to i32"
}

case class IrI32ToI1(result: IRVar, value: IROperand) extends IRStmt {
  override def toLLVMStmt = s"$result = trunc i32 $value to i1"
}

case class IrAdd(result: IRVar, left: IROperand, right: IROperand) extends IRStmt {
  override def toLLVMStmt = s"$result = add i32 $left, $right"
}

case class IrPhi(result: IRVar, values: List[(IROperand, IRLabel)]) extends IRStmt {
  override def toLLVMStmt = s"$result = phi i32 ${values.map(v => s"[ ${v._1}, %${v._2.value} ]").mkString(", ")}"
}

case class IrCondBranch(cond: IROperand, ifTrue: IRLabel, ifFalse: IRLabel) extends IRStmt {
  override def toLLVMStmt = s"br i1 $cond, label %${ifTrue.value}, label %${ifFalse.value}"
}

case class IrBranch(dest: IRLabel) extends IRStmt {
  override def toLLVMStmt = s"br label %${dest.value}"
}


sealed trait IROperand extends IR

case class IRVar(name: String) extends IROperand {
  override def toString: String = name
}

case class IRConstInt(value: Int) extends IROperand {
  override def toString: String = value.toString
}