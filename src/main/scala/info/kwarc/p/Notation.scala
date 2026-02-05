package info.kwarc.p

case class Notation(fixity: Fixity, symbol: String)

abstract class Fixity
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

object Precedence {
  /** Booleans to Booleans */
  val conjunctionLike = -20
  val arrowLike = -20
  /** values to Booleans */
  val equalityLike = -10
  /** values to values, weak-binding */
  val additionLike = 0
  /** values to values, normal-binding */
  val multiplicationLike = 10
  /** values to values, tight-binding */
  val exponentiationLike = 20

  val thin = "°^'`´\""
  val connective = "&|"
  def get(s: String): Int = {
    if (s.length == 1) {
      Unicode.symbolType(s(0)) match {
        case InfixSymbol(p) => return p
        case _ =>
      }
    }
    // TODO classify unicode symbols, maybe use https://www.w3.org/TR/mathml-core/#operator-dictionary-human
    val p = if (s.forall(c => thin.contains(c))) exponentiationLike
    else if (s.forall(c => connective.contains(c))) conjunctionLike
    // =>, <=, ->, <-
    else if ((s.startsWith("<") || s.endsWith(">")) && s.exists(c => c != '<' && c != '>')) arrowLike
    // ==, !=, =<, >=, <>
    else if (s.contains("=") || s.contains('~') || s.contains('<') || s.contains('>')) equalityLike
    else if (s.contains("+") || s.contains("-")) additionLike
    else if (s.contains("*") || s.contains("/")) multiplicationLike
    else additionLike
    p - s.length
  }
}

abstract class SymbolType
case object NullfixSymbol extends SymbolType
case object PrefixSymbol extends SymbolType
case object BindfixSymbol extends SymbolType
case class InfixSymbol(prededence: Int) extends SymbolType
object InfixSymbol {
  /** Booleans to Booleans */
  val conjunctionLike = InfixSymbol(-20)
  val arrowLike = InfixSymbol(-20)
  /** values to Booleans */
  val equalityLike = InfixSymbol(-10)
  /** values to values, weak-binding */
  val additionLike = InfixSymbol(0)
  /** values to values, normal-binding */
  val multiplicationLike = InfixSymbol(10)
  /** values to values, tight-binding */
  val exponentiationLike = InfixSymbol(20)
}
case object PostfixSymbol extends SymbolType
case class OpenBracketSymbol(close: Unicode.UChar) extends SymbolType
case object GeneralOperatorSymbol extends SymbolType
case object NonOperatorSymbol extends SymbolType