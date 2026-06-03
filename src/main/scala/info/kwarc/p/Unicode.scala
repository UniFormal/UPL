package info.kwarc.p

import scala.scalajs.js.|

/**
 * abstract over JVM's internal representation of Char as UTF-16, where Unicode above FFFF is represented as 2 characters
 */
object Unicode {
  type UChar = Int

  @inline def forall(s: String)(f: UChar => Boolean) = s.codePointStepper.iterator.forall(f)

  import Character._

  val symbolCategories = List(CURRENCY_SYMBOL, MATH_SYMBOL, DASH_PUNCTUATION, OTHER_PUNCTUATION, OTHER_SYMBOL)
  val modifierCategories = List(MODIFIER_LETTER, MODIFIER_SYMBOL)

  /** binder symbols cannot be defined based on Unicode classes
   * we take all symbols called "N-Ary" in their Unicode name plus the quantifiers */
  val bindChars: List[UChar] = {
    // n-ary
    List(0x2140, 0x220F, 0x2210, 0x2211, 0x22C0, 0x22C1, 0x22C2, 0x22C3, 0x2A00, 0x2A01, 0x2A02, 0x2A03, 0x2A04, 0x2A05, 0x2A06, 0x2A09, 0x2AFF) :::
      // quantifiers
      List(0x2200, 0x2203, 0x2204) :::
      // integrals
      Range(0x222B, 0x2234).toList
  }

  /** the matching closing bracket, if any
   *
   * '‚' and '„' are open punctuation without corresponding closing punctuation
   * some horizontal brackets have partners that are their vertical mirrors
   * '[' and '{' have legacy codepoints
   * square brackets with ticks in corners (0x298D-0x2990) have their mirror images in the wrong order
   * all other open punctuation has the closing mirror image right afterwards
   */
  def closingBracketFor(c: UChar): Option[UChar] = {
    if (Character.getType(c) != START_PUNCTUATION || !Character.isMirrored(c)) None
    else if (c == '[') Some(']')
    else if (c == '{') Some('}')
    else if (c == 0x298D) Some(0x2990)
    else if (c == 0x298F) Some(0x298E)
    else Some(c+1)
  }
  def openingBracketFor(c: UChar): Option[UChar] = {
    if (Character.getType(c) != END_PUNCTUATION || !Character.isMirrored(c)) None
    else if (c == ']') Some('[')
    else if (c == '}') Some('{')
    else if (c == 0x2990) Some(0x298D)
    else if (c == 0x298E) Some(0x298F)
    else Some(c-1)
  }
}