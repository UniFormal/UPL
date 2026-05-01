package info.kwarc.p.compiler

sealed trait IR

case class IRProgram(
                      structs: List[IRStruct],
                      declaredFunctions: List[IRFun],
                      functions: List[IRFun]
) extends IR

case class IRFun(
    name: String,
    ret: String,
    params: List[String],
    stmts: List[IRStmt]
) extends IR {
  def toLLVM(): String =
    s"""
       |define $ret @$name(${params.mkString(", ")}) {
       |${stmts.map(s => s.toLLVM()).mkString("\n")}
       |}"""
      .stripMargin
  def toLLVMDecl(): String =
    s"""
       |declare $ret @$name(${params.mkString(", ")})""".stripMargin
}

case class IRStruct(
    name: String,
    fields: List[(String, String)]
) extends IR {
  def toLLVMStrct(): String =
    s"%$name = type { ${fields.map(f => f._2).mkString(", ")} }"
}

sealed trait IRStmt extends IR {
  def indentation() = true

  def toLLVMStmt: String

  def toLLVM(): String =
    if (indentation()) s"\t$toLLVMStmt"
    else toLLVMStmt
}

case class IRReturn(value: IROperand) extends IRStmt {
  override def toLLVMStmt = s"ret ${value.llvmType()} $value"
}

case class IRLabel(value: String) extends IRStmt {
  override def indentation() = false

  override def toLLVMStmt = s"$value:"
}

case class IRCmp(result: I32, cond: String, left: IROperand, right: IROperand)
    extends IRStmt {
  override def toLLVMStmt = s"$result = icmp $cond i32 $left, $right"
}

case class IRAdd(result: I32, left: IROperand, right: IROperand) extends IRStmt {
  override def toLLVMStmt = s"$result = add ${result.llvmType()} $left, $right"
}

case class IRSub(result: I32, left: IROperand, right: IROperand) extends IRStmt {
  override def toLLVMStmt = s"$result = sub ${result.llvmType()} $left, $right"
}

case class IRI1toI32(result: I32, value: IROperand) extends IRStmt {
  override def toLLVMStmt = s"$result = zext i1 $value to i32"
}

case class IRI32ToI1(result: I32, value: IROperand) extends IRStmt {
  override def toLLVMStmt = s"$result = trunc i32 $value to i1"
}

case class IrCall(result: IROperand, fun: IRFun, params: List[IROperand]) extends IRStmt {
  override def toLLVMStmt = s"$result = call ${fun.ret} @${fun.name}(${params.map(p => s"${p.llvmType()} $p").mkString(", ")})"
}

case class IrPtrCall(result: IROperand, retTp: String, ptr: IRVarPtr, params: List[IROperand]) extends IRStmt {
  override def toLLVMStmt = s"$result = call $retTp $ptr(${params.map(p => s"${p.llvmType()} $p").mkString(", ")})"
}

case class IRPhi(result: IROperand, values: List[(IROperand, IRLabel)])
    extends IRStmt {
  override def toLLVMStmt =
    s"$result = phi ${result.llvmType()} ${values.map(v => s"[ ${v._1}, %${v._2.value} ]").mkString(", ")}"
}

case class IRCondBranch(cond: IROperand, ifTrue: IRLabel, ifFalse: IRLabel)
    extends IRStmt {
  override def toLLVMStmt =
    s"br i1 $cond, label %${ifTrue.value}, label %${ifFalse.value}"
}

case class IRBranch(dest: IRLabel) extends IRStmt {
  override def toLLVMStmt = s"br label %${dest.value}"
}

case class IRComputeSize(result: I64, struct: IRStruct) extends IRStmt {
  override def toLLVMStmt: String = s"$result = ptrtoint %${struct.name}* getelementptr (%${struct.name}, %${struct.name}* null, i32 1) to i64"
}

case class IRGetElement(result: IRVarPtr, struct: IRStruct, ptr: IRVarPtr, index: Int) extends IRStmt {
  override def toLLVMStmt: String = s"$result = getelementptr %${struct.name}, ptr $ptr, i32 0, i32 $index"
}

case class IRStore(op: IROperand, ptr: IRVarPtr) extends IRStmt {
  override def toLLVMStmt: String = s"store ${op.llvmType()} $op, ptr %${ptr.name}"
}

case class IRLoad(result: IROperand, ptr: IRVarPtr) extends IRStmt {
  override def toLLVMStmt: String = s"$result = load ${result.llvmType()}, ptr %${ptr.name}"
}

trait IROperand extends IR {
  def llvmType(): String
}

trait IRVar extends IROperand {
}

trait IRPtr extends IRVar {
  override def llvmType(): String = "ptr"
}

// TODO combine I32 and I64 into generic
case class I32(name: String) extends IRVar {
  override def toString: String = s"%$name"
  override def llvmType(): String = "i32"
}

case class I64(name: String) extends IRVar {
  override def toString: String = s"%$name"
  override def llvmType(): String = "i64"
}

case class IRVarPtr(name: String) extends IRPtr {
  override def toString: String = s"%$name"
}

case class IRFunPtr(fun: IRFun) extends IRPtr {
  override def toString: String = s"@${fun.name}"
}

case class IRConstInt(value: Int) extends IROperand {
  override def toString: String = value.toString

  override def llvmType(): String = "i32"
}