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
  class Location(uri: Uri, rangeOrPosition: Position) extends js.Object
  @js.native
  class Range(val start: VSCode#Position, val end: VSCode#Position) extends js.Object
  @js.native
  trait Selection extends js.Object {
    def start: Position = js.native
    def end: Position = js.native
  }
  @js.native
  class Hover(text: String) extends js.Object
  @js.native
  class DocumentSymbol(name: String, detail: String, kind: Int, range: Range, selectionRange: Range) extends js.Object {
    var children: js.Array[VSCode#DocumentSymbol] = js.native
  }
  @js.native
  class SignatureHelp() extends js.Object

  def window: Window = js.native
}

@js.native
trait Window extends js.Object {
  def activeTextEditor: TextEditor = js.native
}

@js.native
trait TextEditor extends js.Object {
  def selection: VSCode#Selection = js.native
  def selections: js.Array[VSCode#Selection] = js.native
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
trait DiagnosticCollection extends js.Object {
  def set(uri: Uri, errors: js.Array[VSCode#Diagnostic]): Unit = js.native
}

@js.native
trait Uri extends js.Object

@JSExportTopLevel("VSCodeBridge")
@JSExportAll
class VSCodeBridge(vs: VSCode, diagn: DiagnosticCollection) {
  import vs._
  private def makeOrigin(d: TextDocument) = SourceOrigin(d.fileName)
  val proj = new Project(Nil, None)
  def update(doc: TextDocument) = {
    // println("parsing " + doc.fileName)
    val so = makeOrigin(doc)
    val txt = doc.getText()
    val txtU = if (doc.fileName.endsWith(".tex")) Tex.detexify(txt) else txt
    proj.update(so, txtU)
    proj.check(so)
    val pe = proj.get(so)
    val diags = pe.errors.getErrors.map {e =>
      val rg = range(doc, e.loc)
      new Diagnostic(rg, e.getMessage)
    }
    diagn.set(doc.uri, js.Array(diags:_*))
  }
  def symbols(doc: TextDocument): js.Array[VSCode#DocumentSymbol] = {
    val voc = proj.get(makeOrigin(doc)).getVocabulary
    js.Array(voc.decls.map(d => makeSymbol(doc,d)):_*)
  }
  private def makeSymbol(doc: TextDocument, decl: Declaration): VSCode#DocumentSymbol = {
    val f = doc.positionAt(decl.loc.from)
    val selRg = new Range(f,f)
    val rg = range(doc,decl.loc)
    decl match {
      case m: Module =>
        val kind = if (m.closed) 4 else 3
        val sym = new DocumentSymbol(m.name, "", kind, rg, selRg)
        val chs = m.decls.map(d => makeSymbol(doc,d))
        sym.children = js.Array(chs:_*)
        sym
      case i: Include =>
        val name = if (i.realize) "realize" else "include"
        val kind = 10 // "interface", nothing better available
        new DocumentSymbol(name, i.dom.toString, kind, rg, selRg)
      case sd: SymbolDeclaration =>
        val detail = sd match {
          case _:TypeDecl => ": type"
          case ed:ExprDecl => ": " + ed.tp.toString
        }
        new DocumentSymbol(sd.name, detail, 7, rg, selRg)
    }
  }

  def definitionLocation(doc: TextDocument, pos: Position): VSCode#Location = {
    null
  }
  def signatureHelp(doc: TextDocument, pos: Position): VSCode#SignatureHelp = {
    null
  }

  def hover(doc: TextDocument, pos: Position): VSCode#Hover = reportExceptions {
    val so = makeOrigin(doc)
    val offset = doc.offsetAt(pos)
    val defaultLoc = info.kwarc.p.Location(so, offset, offset)
    val loc = vs.window.activeTextEditor.selections.headOption match {
      case Some(s) =>
        val sl = info.kwarc.p.Location(so,doc.offsetAt(s.start),doc.offsetAt(s.end))
        if (sl contains defaultLoc) sl else defaultLoc
      case None => defaultLoc
    }
    val (gc,sf) = proj.fragmentAt(loc).getOrElse(return null)
    //return new Hover("line: " + pos.line + "; character: " + pos.character + "\n" + sf.toStringShort)
    val hov = sf match {
      case e: Expression =>
        val tp = new Checker(ErrorThrower).inferCheckedExpression(gc,e)
        tp.toString
      case tp: Type => tp.toString
      case _ => sf.toString
    }
    new Hover(hov)
  }

  @inline
  private def reportExceptions[A](code: => A) =
    try {code}
    catch {
      case e: Error => println(e.getMessage); e.printStackTrace(); throw e
      case e: Exception => println(e.getMessage); e.printStackTrace(); throw e
    }

  private def range(doc: TextDocument, loc: info.kwarc.p.Location) = new Range(doc.positionAt(loc.from), doc.positionAt(loc.to))
}

