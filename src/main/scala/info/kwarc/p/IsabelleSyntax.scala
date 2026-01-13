package info.kwarc.p




abstract class Isa {


}

case class IsaTheory(value: Module, decls: IsaBody) extends Isa {
  override def toString = s"theory ${value.name}\n" +
    s"  imports Main\n" +
    s"begin\n\n" +
    decls.toString +
    s"end"
}

case class IsaBody(decls: List[Isa]) extends Isa {
  override def toString = decls.mkString("\n\n") + "\n\n"
}

case class IsaDefiniton(value: ExprDecl) extends Isa {
  override def toString = s"definition ${value.name} :: ${value.tp} where\n" +
    s"  \"${value.name} = ${value.dfO.get}\""
}

case class IsaInt(value: Int) extends Isa {
  override def toString = value.toString
}

case class IsaBool(value: Boolean) extends Isa {
  override def toString = value.toString
}