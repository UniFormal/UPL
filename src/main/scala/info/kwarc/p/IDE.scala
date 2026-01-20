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
  class Location(uri: Uri, rangeOrPosition: VSCode#Position) extends js.Object
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
  class SignatureHelp() extends js.Object {
    var signatures: js.Array[SignatureInformation] = js.native
  }
  @js.native
  class SignatureInformation(label: String, documentation: String) extends js.Object
  @js.native
  class CompletionItem(label: String) extends js.Object

  def window: Window = js.native
  def workspace: Workspace = js.native
}

@js.native
trait Window extends js.Object {
  def activeTextEditor: TextEditor = js.native
}

@js.native
trait Workspace extends js.Object {
  def textDocuments: js.Array[TextDocument] = js.native
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
  def languageId: String = js.native
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
trait Uri extends js.Object {
  def scheme: String = js.native
  def path: String = js.native
  def fragment: String = js.native
}

@JSExportTopLevel("VSCodeBridge")
@JSExportAll
class VSCodeBridge(vs: VSCode, diagn: DiagnosticCollection) {
  import vs._

  val proj = new Project(Nil)

  private def makeOrigin(d: TextDocument) = {
    if (d.uri.scheme == "vscode-notebook-cell") {
      SourceOrigin(d.fileName, d.uri.fragment)
    } else {
      SourceOrigin(d.fileName)
    }
  }

  def update(doc: TextDocument): Unit = reportExceptions {
    if (doc.languageId != "upl") return
    // println("parsing " + doc.fileName)
    val so = makeOrigin(doc)
    val txt = doc.getText()
    val txtU = if (doc.fileName.endsWith(".tex")) Tex.detexify(txt) else txt
    proj.update(so,txtU)
    proj.check(so, false)
    val pe = proj.get(so)
    val diags = pe.errors.getErrors.map {e =>
      // TODO: Catch errors with e.loc == null
      val rg = range(doc,e.loc)
      new Diagnostic(rg,e.getMessage)
    }
    diagn.set(doc.uri,js.Array(diags: _*))
  }

  def symbols(doc: TextDocument): js.Array[VSCode#DocumentSymbol] = {
    val voc = proj.get(makeOrigin(doc)).getVocabulary
    js.Array(voc.decls.map(d => makeSymbol(doc,d)): _*)
  }

  private def makeSymbol(doc: TextDocument,decl: Declaration): VSCode#DocumentSymbol = {
    val f = doc.positionAt(decl.loc.from)
    val selRg = new Range(f,f)
    val rg = range(doc,decl.loc)
    decl match {
      case m: Module =>
        val kind = if (m.closed) 4 else 3
        val sym = new DocumentSymbol(m.name,"",kind,rg,selRg)
        val chs = m.decls.map(d => makeSymbol(doc,d))
        sym.children = js.Array(chs: _*)
        sym
      case i: Include =>
        val name = if (i.realize) "realize" else "include"
        val kind = 10 // "interface", nothing better available
        new DocumentSymbol(name,i.dom.toString,kind,rg,selRg)
      case sd: SymbolDeclaration =>
        val detail = sd match {
          case _: TypeDecl => ": type"
          case ed: ExprDecl => ": " + ed.tp.toString
        }
        new DocumentSymbol(sd.name,detail,7,rg,selRg)
    }
  }

  def definitionLocation(doc: TextDocument,pos: Position): VSCode#Location = {
    val (gc,sf) = fragmentAt(doc,pos).getOrElse {
      return null
    }
    val ndO = sf match {
      case r: Ref => gc.lookupRef(r)
      case _ => return null
    }
    ndO.flatMap(nd => Option(nd.loc)) match {
      case Some(l) =>
        val lDoc = vs.workspace.textDocuments.find(d => makeOrigin(d) == l.origin).getOrElse {
          return null
        }
        new Location(lDoc.uri,lDoc.positionAt(l.from))
      case None => null
    }
  }

  def signatureHelp(doc: TextDocument,pos: Position): VSCode#SignatureHelp = {
    val (gc,sf) = fragmentAt(doc,pos).getOrElse {
      return null
    }
    val funDecl = sf match {
      case Application(r: Ref,_) => gc.lookupRef(r).getOrElse {
        return null
      }
      case _ => return null
    }
    funDecl match {
      case ed: ExprDecl =>
        val sh = new SignatureHelp()
        sh.signatures = js.Array(new SignatureInformation(ed.name,ed.tp.toString))
        sh
      case _ => null
    }
  }

  def complete(doc: TextDocument,pos: Position): js.Array[VSCode#CompletionItem] = {
    val (gc,sf) = fragmentAt(doc,pos).getOrElse {
      return null
    }
    val locals = gc.visibleLocals.domain
    val thy = sf match {
      case oo: OwnedObject => oo.ownerDom
      case oo: ObjectOver => oo.scope
      case _ => gc.currentRegion.theory
    }
    val regionals = thy.decls.flatMap {
      case sd: NamedDeclaration => List(sd.name)
      case i: Include => if (thy.isFlat) Nil else Checker.evaluateTheory(gc,i.dom).domain
    }
    val cs = (locals ::: regionals).distinct.map(n => new CompletionItem(n))
    js.Array(cs: _*)
  }

  def fragmentAt(d: TextDocument,p: Position) = {
    val o = d.offsetAt(p)
    proj.fragmentAt(info.kwarc.p.Location(makeOrigin(d),o,o))
  }

  def hover(doc: TextDocument,pos: Position): VSCode#Hover = reportExceptions {
    val so = makeOrigin(doc)
    val offset = doc.offsetAt(pos)
    val defaultLoc = info.kwarc.p.Location.single(so,offset)
    var selection = false
    val loc = vs.window.activeTextEditor.selections.headOption match {
      case Some(s) =>
        val sL = info.kwarc.p.Location(so,doc.offsetAt(s.start),doc.offsetAt(s.end))
        if (sL contains defaultLoc) {selection = true; sL} else defaultLoc
      case None => defaultLoc
    }
    val (gc,sf) = proj.fragmentAt(loc).getOrElse(return null)
    // return new Hover("line: " + pos.line + "; character: " + pos.character + "\n" + sf.toStringShort + " " + sf.loc)
    val hov = sf match {
      case r: Ref => gc.lookupRef(r).getOrElse(return null) match {
        case sd: SymbolDeclaration => sd.toString
        case m: Module => "module"
        case vd: EVarDecl => vd.toString
      }
      case vd: EVarDecl => vd.toString
      case bo: BaseOperator => bo.operator.symbol + ": " + bo.tp.toString
      case e: Expression if selection =>
        try {new Checker(ErrorThrower).inferCheckedExpression(gc,e).toString}
        catch {case e: PError => "inference error: " + e.getMessage}
      case tp: Type => tp.toString
      case _ => return null // sf.toString
    }
    new Hover(hov)
  }

  def interpretCell(doc: TextDocument) = {
    val so = makeOrigin(doc)
    try {
      proj.check(so,true).toString
    } catch {
      case e: PError => e.getMessage
    }
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

