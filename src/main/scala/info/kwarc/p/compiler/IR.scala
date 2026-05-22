package info.kwarc.p.compiler

case class IRProgram(
    structs: List[IRStruct],
    declaredFunctions: List[IRDeclFun],
    functions: List[IRFun]
)

case class IRStruct(
    name: String,
    fields: List[IrType]
) {
  def render(): String =
    s"%$name = type { ${fields.map { f => f.render() }.mkString(", ")} }"
}

case class IRDeclFun(
    name: String,
    retTp: IrType,
    paramsTp: List[IrType]
) {
  def render(): String =
    s"""|declare ${retTp.render()} @$name(${paramsTp
      .map { p => s"${p.render()}" }
      .mkString(", ")})""".stripMargin
}

case class IRFun(
    name: String,
    retTp: IrType,
    params: List[IrVar],
    blocks: List[IrBlock]
) {
  def render(): String =
    s"""|define ${retTp.render()} @$name(${params
      .map { p => s"${p.tp.render()} ${p.render()}" }
      .mkString(", ")}) {
       |${blocks.map(_.render()).mkString("\n")}
       |}""".stripMargin
}

case class IrBlock(
    label: String,
    instructions: List[IrInstr]
) {
  def render(): String =
    s"""|$label:
       |${instructions.map(i => s"\t${i.render()}").mkString("\n")}""".stripMargin
}

sealed trait IrInstr {
  def render(): String
}

case class IrReturn(value: IrOperand) extends IrInstr {
  override def render(): String =
    s"ret ${value.tp.render()} ${value.render()}"
}

case class IrICmp(result: IrVar, cond: Condition, left: IrOperand, right: IrOperand) extends IrInstr {
  override def render(): String =
    s"${result.render()} = icmp ${cond.label} ${left.tp.render()} ${left.render()}, ${right.render()}"
}

sealed abstract class Condition(val label: String)
object Condition {
  case object EQUAL extends Condition("eq")
  case object NOT_EQUAL extends Condition("ne")
  case object SIGNED_GREATER_THAN extends Condition("sgt")
  case object SIGNED_GREATER_EQUAL extends Condition("sge")
  case object SIGNED_LESS_THAN extends Condition("slt")
  case object SIGNED_LESS_EQUAL extends Condition("sle")
}

case class IrCondBranch(cond: IrOperand, ifTrue: String, ifFalse: String)
  extends IrInstr {
  override def render() =
    s"br i1 ${cond.render()}, label %$ifTrue, label %$ifFalse"
}

case class IRBranch(dest: String) extends IrInstr {
  override def render() = s"br label %$dest"
}

case class IrPhi(result: IrOperand, values: List[(IrOperand, String)])
  extends IrInstr {
  override def render() =
    s"${result.render()} = phi ${result.tp.render()} ${values.map(v => s"[ ${v._1.render()}, %${v._2} ]").mkString(", ")}"
}

sealed trait IrType {
  def render(): String
}

case class IrIntType(bits: Int) extends IrType {
  override def render(): String = s"i$bits"
}

object IrIntType {
  val I64 = IrIntType(64)
  val I1 = IrIntType(1)
}

case class IrPtrType(to: IrType) extends IrType {
  override def render(): String = "ptr"
}

sealed trait IrOperand {
  def render(): String
  def tp: IrType
}

case class IrVar(override val tp: IrType, name: String) extends IrOperand {
  override def render(): String = s"%$name"
}

case class IrConst(override val tp: IrType, value: Long) extends IrOperand {
  override def render(): String = s"$value"
}

object IrConst {
  def apply(value: Long) = new IrConst(IrIntType.I64, value)
  def apply(value: Boolean) = new IrConst(IrIntType.I1, if (value) 1 else 0)
}
