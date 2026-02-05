package info.kwarc.p

import scala.scalajs.js.|

/**
 * abstract over JVM's internal representation of Char as UTF-16, where Unicode above FFFF is represented as 2 characters
 */
object Unicode {
  type UChar = Int
  @inline def forall(s: String)(f: UChar => Boolean) = s.codePointStepper.iterator.forall(f)
  @inline def characters(s: String) = s.codePointStepper.iterator.toList
  @inline def toString(c: UChar) = Character.toChars(c).mkString("")

  import Character._
  import Character.UnicodeBlock._
  val symbolCategories = List(CURRENCY_SYMBOL, MATH_SYMBOL, DASH_PUNCTUATION, OTHER_PUNCTUATION, OTHER_SYMBOL)
  val modifierCategories = List(MODIFIER_LETTER, MODIFIER_SYMBOL)

  /** binder symbols cannot be defined based on Unicode classes
   *  we take all symbols called "N-Ary" in their Unicode name plus the quantifiers */
  val bindChars: List[UChar] = {
    // n-ary
    List(0x2140,0x220F,0x2210,0x2211,0x22C0,0x22C1,0x22C2,0x22C3,0x2A00,0x2A01,0x2A02,0x2A03,0x2A04,0x2A05,0x2A06,0x2A09,0x2AFF) :::
    // quantifiers
    List(0x2200,0x2203,0x2204) :::
    // integrals
    Range(0x222B,0x2234).toList
  }

  /** all characters that are math symbols and are not brackets or binders have this category up to the bound */
  val MATHEMATICAL_OPERATORS_Bounds = List(
    0x2200 -> BindfixSymbol,
    0x2202 -> PrefixSymbol,
    0x2204 -> BindfixSymbol,
    0x2205 -> NullfixSymbol,
    0x220D -> InfixSymbol.equalityLike,
    0x220E -> NullfixSymbol,
    0x2211 -> BindfixSymbol,
    0x2214 -> InfixSymbol.additionLike,
    0x2219 -> InfixSymbol.multiplicationLike,
    0x221C -> PrefixSymbol,
    0x2226 -> InfixSymbol.equalityLike,
    0x2228 -> InfixSymbol.conjunctionLike,
    0x222A -> InfixSymbol.additionLike,
    0x2234 -> BindfixSymbol,
    0x2237 -> InfixSymbol.equalityLike,
    0x2249 -> InfixSymbol.additionLike,
    0x228B -> InfixSymbol.equalityLike,
    0x228E -> InfixSymbol.additionLike,
    0x2292 -> InfixSymbol.equalityLike,
    0x2296 -> InfixSymbol.additionLike,
    0x229B -> InfixSymbol.multiplicationLike,
    0x229C -> InfixSymbol.equalityLike,
    0x229F -> InfixSymbol.additionLike,
    0x22A1 -> InfixSymbol.multiplicationLike,
    0x22AF -> PrefixSymbol,
    0x22B5 -> InfixSymbol.equalityLike,
    0x22B8 -> InfixSymbol.arrowLike,
    0x22BA -> PostfixSymbol,
    0x22BD -> InfixSymbol.conjunctionLike,
    0x22BF -> PrefixSymbol,
    0x22C3 -> BindfixSymbol,
    0x22CC -> InfixSymbol.multiplicationLike,
    0x22CD -> InfixSymbol.equalityLike,
    0x22CF -> InfixSymbol.conjunctionLike,
    0x22D1 -> InfixSymbol.equalityLike,
    0x22D3 -> InfixSymbol.additionLike,
    0x22ED -> InfixSymbol.equalityLike,
    0x22F1 -> InfixSymbol.multiplicationLike,
    0x22FF -> InfixSymbol.equalityLike
  )
  def findIn(bs: List[(UChar,SymbolType)], c: UChar): SymbolType = {
    bs foreach {case (b, r) => if (c <= b) return r}
    InfixSymbol.additionLike // should be impossible
  }

  /** the matching closing bracket, if any
   *
   *  '‚' and '„' are open punctuation without corresponding closing punctuation
   *  some horizontal brackets have partners that are their vertical mirrors
   *  '[' and '{' have legacy codepoints
   *  square brackets with ticks in corners (0x298D-0x2990) have their mirror images in the wrong order
   *  all other open punctuation has the closing mirror image right afterwards
   */
  def closingBracketSymbol(c: UChar): Option[UChar] = {
    if (Character.getType(c) != START_PUNCTUATION || !Character.isMirrored(c)) None
    else if (c == '[') Some(']')
    else if (c == '{') Some('}')
    else if (c == 0x298D) Some(0x2990)
    else if (c == 0x298F) Some(0x298E)
    else Some(c+1)
  }

  def symbolType(c: UChar): SymbolType = {
    // special cases for basic symbols: too widely used to fix their type here
    c match {
      case '#' | '$' | '%'  | '@' | '!' | '?' | '-' | '+' => return GeneralOperatorSymbol
      case '*' | '/' => return GeneralOperatorSymbol
      case '=' | '<' | '>' =>return GeneralOperatorSymbol
      case '^' | ':' => return GeneralOperatorSymbol
      case '&' | '|' => return GeneralOperatorSymbol
      case _ =>
    }

    // special case: binders
    if (bindChars.contains(c)) return BindfixSymbol

    // special case: brackets
    closingBracketSymbol(c).foreach {cls => return OpenBracketSymbol(cls)}

    val b = UnicodeBlock.of(c)
    // decision based on block
    b match {
      case SUPERSCRIPTS_AND_SUBSCRIPTS => return PostfixSymbol
      case _ =>
    }
    // decision based on type
    val t = Character.getType(c)
    t match {
      case DASH_PUNCTUATION | OTHER_PUNCTUATION | MODIFIER_LETTER | MODIFIER_SYMBOL => PostfixSymbol
      case CURRENCY_SYMBOL | OTHER_SYMBOL => InfixSymbol.additionLike
      case MATH_SYMBOL => b match {
        case LATIN_1_SUPPLEMENT =>
          if (c == '±') InfixSymbol.additionLike
          else if (c == '¬') PrefixSymbol
          else if (c == '×' || c == '÷') InfixSymbol.multiplicationLike
          else InfixSymbol.equalityLike
        case GREEK_EXTENDED | COPTIC => InfixSymbol.equalityLike // only ϶
        case ARABIC => PostfixSymbol
        case GENERAL_PUNCTUATION => InfixSymbol.conjunctionLike
        case SUPERSCRIPTS_AND_SUBSCRIPTS => PostfixSymbol
        case LETTERLIKE_SYMBOLS =>
          if (c == 0x2118) PrefixSymbol
          else if (c == 0x2140) BindfixSymbol
          else if (c == 0x214B) InfixSymbol.conjunctionLike
          else NullfixSymbol
        case MATHEMATICAL_OPERATORS => findIn(MATHEMATICAL_OPERATORS_Bounds,c)
        case MISCELLANEOUS_MATHEMATICAL_SYMBOLS_A =>
          // TODO: finer classification
          InfixSymbol.equalityLike
        case MISCELLANEOUS_MATHEMATICAL_SYMBOLS_B =>
          // TODO: finer classification
          InfixSymbol.additionLike
        case SUPPLEMENTAL_MATHEMATICAL_OPERATORS =>
          // TODO: finer classification
          InfixSymbol.multiplicationLike
        case ARROWS | SUPPLEMENTAL_ARROWS_A | SUPPLEMENTAL_ARROWS_B | SUPPLEMENTAL_ARROWS_C =>
          InfixSymbol.arrowLike
        case GEOMETRIC_SHAPES | GEOMETRIC_SHAPES_EXTENDED =>
          NullfixSymbol
        case MISCELLANEOUS_SYMBOLS =>
          InfixSymbol.additionLike
        case MISCELLANEOUS_SYMBOLS_AND_ARROWS =>
          // many of these are not in category Math
          InfixSymbol.arrowLike
        case MISCELLANEOUS_TECHNICAL =>
          InfixSymbol.additionLike
        case HALFWIDTH_AND_FULLWIDTH_FORMS =>
          if (c <= 0xFF60) {
            // full width
            InfixSymbol.additionLike
          } else {
            // half width
            InfixSymbol.exponentiationLike
          }
        case SMALL_FORM_VARIANTS =>
          PostfixSymbol
        case _ =>
          throw IError("missing case for symbol: " + c.toChar)
      }
      case _ => NonOperatorSymbol
    }
  }
}
