package info.kwarc.p

case class Notation(fixity: Fixity, symbol: String)

abstract class Fixity
case object Infix extends Fixity
case object Prefix extends Fixity
case object Postfix extends Fixity
case object Circumfix extends Fixity
case object Bindfix extends Fixity


