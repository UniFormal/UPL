package info.kwarc.p

/**
  * An abstraction of source files
  *  - avoids dependency on java.io.File
  *  - allows representation of non-file sources, like
  *   - notebook cells
  *   - REPL inputs
  *   - the FrameIT SituationTheory
  */
sealed trait SourceOrigin{
  /**
    * Toplevel declarations of a global source are in the context for all other sources
    * Non global sources may override [[inContextFor]] to give visibility conditions
    */
  def global: Boolean
  /** Are the toplevel declarations in this source visible from the other Source? */
  def inContextFor(other: SourceOrigin): Boolean
}

/** A source where toplevel declarations are globally visible */
trait GlobalSource extends SourceOrigin{
  def global: Boolean = true
  def inContextFor(other: SourceOrigin): Boolean = this != other
}

/** An independent Source
  * @example Files
  * @param source an identifier of this source, such as a file path or URL
  */
case class StandaloneSource(source: String) extends GlobalSource {
  override def toString: String = source
}

/** An anonymous source, behaves like a [[StandaloneSource]], but is guaranteed to always be unique.
  * @example inputs to an interactive Interpreter
  */
final case class AnonymousSource private (id: Int) extends GlobalSource {
  override def toString: String = s"??$id"
}
object AnonymousSource{
  def global: Boolean = false
  private var counter = -1
  /**  */
  private def apply(id: Int): AnonymousSource = {
    counter += 1
    new AnonymousSource(counter)
  }

  def getNew: AnonymousSource = {
    counter += 1
    new AnonymousSource(counter)
  }
}

/** A code fragment that is not visible for all others. */
trait LocalSource extends SourceOrigin{
  def global: Boolean = false
}

/** A small code fragment; toplevel declarations are visible only for other fragments of the same source
  * @example Cells of a notebook-file
  * @param source an identifier shared by all fragments of the same source, such as a file path or URL
  * @param fragment an identifier of the fragment
  */
case class SourceFragment(source: String, fragment: String) extends LocalSource {
  override def toString: String = source + "#" + fragment

  def inContextFor(other: SourceOrigin): Boolean = other match {
    case SourceFragment(otherSource, otherFragment)
      if otherSource == source && otherFragment != fragment => true
    case _ => false
  }
}

/** TmpSource is a volatile Source, that (semantically) is not actually stored.
  * Its declarations are not visible to any other Source, and a [[ProjectEntry]]([[TmpSource]])
  * can be overwritten without consequences.
  * @example - parse/check/evaluate some input, without affecting the project
  *          - REPL lines
  */
case object TmpSource extends LocalSource {
  def inContextFor(other: SourceOrigin): Boolean = false
}
