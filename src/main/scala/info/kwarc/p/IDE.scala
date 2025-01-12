package info.kwarc.p

import scala.scalajs.js
import js.annotation._

@js.native
trait VSCode extends js.Object {
  @js.native
  class Diagnostic(range: VSCode#Range, msg: String) extends js.Object
  @js.native
  class Position(val line: Int, val character: Int) extends js.Object
  @js.native
  class Range(val start: VSCode#Position, val end: VSCode#Position) extends js.Object
  @js.native
  class Hover(text: String) extends js.Object
}

@js.native
trait DiagnosticCollection extends js.Object {
  def set(uri: Uri, errors: js.Array[VSCode#Diagnostic]): Unit = js.native
}

@js.native
trait TextDocument extends js.Object {
  // using val resulted in receiving undefined fields from Javascript
  def fileName: String = js.native
  def uri: Uri = js.native
  def isDirty: Boolean = js.native
  def getText(): String = js.native
  def positionAt(offset: Int): VSCode#Position = js.native
  def offsetAt(pos: VSCode#Position): Int = js.native
}

@js.native
trait Uri extends js.Object

@JSExportTopLevel("VSCodeBridge")
@JSExportAll
class VSCodeBridge(vs: VSCode, diagn: DiagnosticCollection) {
  import vs._
  val proj = new Project(Nil, None)
  def update(doc: TextDocument) = {
    // println("parsing " + doc.fileName)
    val so = SourceOrigin(doc.fileName)
    proj.update(so, doc.getText())
    proj.check(so)
    val pe = proj.get(so)
    println(pe.errors)
    val diags = pe.errors.getErrors.map {e =>
      val rg = new Range(doc.positionAt(e.loc.from), doc.positionAt(e.loc.to))
      new Diagnostic(rg, e.getMessage)
    }
    diagn.set(doc.uri, js.Array(diags:_*));
  }
  def hover(doc: TextDocument, pos: Position): VSCode#Hover = {
    val so = SourceOrigin(doc.fileName)
    val pe = proj.get(so)
    val offset = doc.offsetAt(pos)
    new Hover("line: " + pos.line + "; character: " + pos.character + "; offset: " + offset)
  }
}

