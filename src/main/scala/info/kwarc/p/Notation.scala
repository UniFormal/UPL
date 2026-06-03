package info.kwarc.p

case class Notation(fixity: Fixity, symbol: String)

abstract class Fixity
case object Nullfix extends Fixity
case object Infix extends Fixity
case object Prefix extends Fixity
case object Postfix extends Fixity
case object Circumfix extends Fixity
case object Applyfix extends Fixity
case object Bindfix extends Fixity

sealed abstract class Associativity
case object NotAssociative extends Associativity
case object Semigroup extends Associativity
case class Monoid(neut: Expression) extends Associativity
case object RightAssociative extends Associativity
case object LeftAssociative extends Associativity

// an operator whose fixity is not yet resolved
case class UnfixedOperator(symbol: String, loc: Location, spaceBefore: Int, spaceAfter: Int, opening: Boolean, closing: Boolean) {
  def attachLeft = spaceBefore < spaceAfter
  def attachRight = spaceBefore > spaceAfter
  def symmetric = spaceBefore == spaceAfter
  def unspaced = spaceBefore == 0 && spaceAfter == 0
  def withFixity(f: Fixity) = PseudoOperator(this, f)
  def toApplication(f: Fixity, args: List[Expression]) = {
    val op = withFixity(f).toExpression
    Application(op, args)
  }
}