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

  def scriptOf(c: UChar) = {
    // This should simply be UnicodeScript.of(c), but that is not supported by Scala.js.
    // In any case, Unicode script doesn't support the block of Mathematical Alphanumeric Symbols (see below).
    // So we need a native implementation anyway.
    if (!Character.isLetter(c)) -1
    else if (c >= 0x0041 && c <= 0x02E4) 1   // LATIN
    else if (c >= 0x0370 && c <= 0x03FF) 100 // GREEK and COPTIC
    else {
      // various extension blocks
      val b = Character.UnicodeBlock.of(c).toString
      if (b.startsWith("LATIN")) 1
      else if (b.startsWith("GREEK")) 100
      // skipping the phonetic extensions U+1D00-U+1DBF
      else if (c >= 0x1D400 && c <= 0x1D7FF) {
        // Mathematical Alphanumeric Symbols, U+1D400-U+1D7FF
        if      (c <= 0x1D433)  2 // bold
        else if (c <= 0x1D467)  3 // italic
        else if (c <= 0x1D49B)  4 // bold, italic
        else if (c <= 0x1D4CF)  5 // script
        else if (c <= 0x1D503)  6 // script, bold
        else if (c <= 0x1D537)  7 // fraktur
        else if (c <= 0x1D56B)  8 // double-struck
        else if (c <= 0x1D59F)  9 // fraktur, bold
        else if (c <= 0x1D5D3) 10 // sans-serif
        else if (c <= 0x1D607) 11  // sans-serif, bold
        else if (c <= 0x1D63B) 12  // sans-serif, italic
        else if (c <= 0x1D66F) 13  // sans-serif, italic, bold
        else if (c <= 0x1D6A3) 14  // monospace
        else if (c <= 0x1D6A5)  3  // italic, dotless variants
        else if (c <= 0x1D6E1) 101 // greek bold (here and below: including a few variants at the end)
        else if (c <= 0x1D71B) 102 // greek, italic
        else if (c <= 0x1D755) 103 // greek, bold, italic
        else if (c <= 0x1D78F) 104 // greek, sans-serif, bold
        else if (c <= 0x1D7C9) 105 // greek, sans-serif, bold, italic
        else 0 // digits
      } else
        0 // other
    }
  }
}