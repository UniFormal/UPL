package info.kwarc.p.lsp

/** Converts between UPL's character-offset [[info.kwarc.p.Location]]s and
  * LSP's (line, UTF-16-code-unit) [[org.eclipse.lsp4j.Position]]s for one
  * document's text.
  *
  * This is the plain-JVM equivalent of what `TextDocument.positionAt`/
  * `offsetAt` did for free in the VS Code extension (see `IDE.scala`).
  */
final class OffsetIndex(text: String) {
  /** lineStarts(i) = offset of the first character of line i (0-based) */
  private val lineStarts: Array[Int] = {
    val buf = scala.collection.mutable.ArrayBuffer(0)
    var i = 0
    while (i < text.length) {
      if (text.charAt(i) == '\n') buf += i + 1
      i += 1
    }
    buf.toArray
  }

  def toOffset(line: Int, character: Int): Int = {
    if (line < 0) 0
    else if (line >= lineStarts.length) text.length
    else {
      val lineEnd = if (line + 1 < lineStarts.length) lineStarts(line + 1) else text.length
      math.min(lineStarts(line) + math.max(0, character), lineEnd)
    }
  }

  def toLineCol(offset: Int): (Int, Int) = {
    val o = math.max(0, math.min(offset, text.length))
    var lo = 0
    var hi = lineStarts.length - 1
    while (lo < hi) {
      val mid = (lo + hi + 1) / 2
      if (lineStarts(mid) <= o) lo = mid else hi = mid - 1
    }
    (lo, o - lineStarts(lo))
  }
}
