package info.kwarc.p.lsp

import java.util.concurrent.CompletableFuture
import java.util.{List => JList}
import scala.jdk.CollectionConverters._

import org.eclipse.lsp4j.{Location => LspLocation, _}
import org.eclipse.lsp4j.jsonrpc.messages.{Either => LEither}
import org.eclipse.lsp4j.services.{LanguageClient, TextDocumentService}

import info.kwarc.p._

/** Implements the per-document LSP requests by delegating to the same
  * [[info.kwarc.p.Project]] API the VS Code extension's `VSCodeBridge`
  * (see `IDE.scala`) uses -- diagnostics, hover, completion, go-to-definition
  * and document outline are all backed by the real parser/checker, not a
  * re-implementation.
  */
class UplTextDocumentService(project: Project) extends TextDocumentService {
  private var client: LanguageClient = _
  def connect(c: LanguageClient): Unit = { client = c }

  /** uri -> (current text, offset<->position index for that text) */
  private val docs = scala.collection.mutable.Map[String, (String, OffsetIndex)]()

  private def origin(uri: String): SourceOrigin = SourceOrigin(uri)

  private def preprocess(uri: String, text: String): String =
    if (uri.endsWith(".tex")) Tex.detexify(text) else text

  private def setText(uri: String, rawText: String): Unit = {
    val text = preprocess(uri, rawText)
    docs(uri) = (text, new OffsetIndex(text))
    checkAndPublish(uri, text)
  }

  private def checkAndPublish(uri: String, text: String): Unit = {
    val so = origin(uri)
    try {
      project.updateAndCheck(so, text)
    } catch {
      // parse/check errors are reported via the ErrorCollector below already;
      // this only guards against genuinely unexpected exceptions crashing the server
      case _: Throwable => ()
    }
    val idx = docs(uri)._2
    val diags = project.get(so).errors.getErrors.map { e =>
      val (l1, c1) = idx.toLineCol(e.loc.from)
      val (l2, c2) = idx.toLineCol(e.loc.to)
      new Diagnostic(new Range(new Position(l1, c1), new Position(l2, c2)), e.getMessage)
    }
    if (client != null) {
      client.publishDiagnostics(new PublishDiagnosticsParams(uri, diags.asJava))
    }
  }

  override def didOpen(params: DidOpenTextDocumentParams): Unit =
    setText(params.getTextDocument.getUri, params.getTextDocument.getText)

  override def didChange(params: DidChangeTextDocumentParams): Unit = {
    // the server advertises full-document sync (see UplLanguageServer), so the
    // last (only) content change always carries the complete new text
    val text = params.getContentChanges.asScala.last.getText
    setText(params.getTextDocument.getUri, text)
  }

  override def didClose(params: DidCloseTextDocumentParams): Unit = {
    val uri = params.getTextDocument.getUri
    docs.remove(uri)
    if (client != null) {
      client.publishDiagnostics(new PublishDiagnosticsParams(uri, java.util.Collections.emptyList()))
    }
  }

  override def didSave(params: DidSaveTextDocumentParams): Unit = ()

  private def fragmentAt(uri: String, pos: Position) =
    docs.get(uri).flatMap { case (_, idx) =>
      val offset = idx.toOffset(pos.getLine, pos.getCharacter)
      project.fragmentAt(info.kwarc.p.Location(origin(uri), offset, offset))
    }

  override def hover(params: HoverParams): CompletableFuture[Hover] =
    CompletableFuture.supplyAsync(() => {
      val descr = fragmentAt(params.getTextDocument.getUri, params.getPosition).flatMap { case (gc, sf) =>
        sf match {
          case r: Ref => gc.lookupRef(r).map {
            case sd: SymbolDeclaration => sd.toString
            case _: Module => "module"
            case vd: VarDecl => vd.toString
          }
          case vd: VarDecl => Some(vd.toString)
          case bo: BaseOperator => Some(bo.operator.symbol + ": " + bo.tp.toString)
          case tp: Type => Some(tp.toString)
          case _ => None
        }
      }
      descr match {
        case Some(s) => new Hover(new MarkupContent("plaintext", s))
        case None => null
      }
    })

  override def definition(params: DefinitionParams)
      : CompletableFuture[LEither[JList[_ <: LspLocation], JList[_ <: LocationLink]]] =
    CompletableFuture.supplyAsync(() => {
      val locO = fragmentAt(params.getTextDocument.getUri, params.getPosition).flatMap { case (gc, sf) =>
        sf match {
          case r: Ref => gc.lookupRef(r).flatMap(nd => Option(nd.loc))
          case _ => None
        }
      }
      val list: JList[LspLocation] = locO match {
        case Some(l) =>
          val defUri = l.origin.container
          val idx = docs.get(defUri).map(_._2)
          val (l1, c1) = idx.map(_.toLineCol(l.from)).getOrElse((0, 0))
          val (l2, c2) = idx.map(_.toLineCol(l.to)).getOrElse((0, 0))
          val range = new Range(new Position(l1, c1), new Position(l2, c2))
          java.util.Collections.singletonList(new LspLocation(defUri, range))
        case None => java.util.Collections.emptyList[LspLocation]()
      }
      LEither.forLeft(list)
    })

  override def completion(params: CompletionParams)
      : CompletableFuture[LEither[JList[CompletionItem], CompletionList]] =
    CompletableFuture.supplyAsync(() => {
      val items: List[CompletionItem] = fragmentAt(params.getTextDocument.getUri, params.getPosition) match {
        case Some((gc, sf)) =>
          val locals = gc.visibleLocals.domain
          val thy = sf match {
            case oo: OwnedObject => oo.ownerDom
            case oo: ObjectOver => oo.scope
            case _ => gc.currentRegion.theory
          }
          val regionals = thy.decls.flatMap {
            case sd: NamedDeclaration => List(sd.name)
            case i: Include => if (thy.isFlat) Nil else Checker.evaluateTheory(gc, i.dom).domain
            case _ => Nil
          }
          (locals ::: regionals).distinct.map(n => new CompletionItem(n))
        case None => Nil
      }
      LEither.forLeft(items.asJava)
    })

  override def signatureHelp(params: SignatureHelpParams): CompletableFuture[SignatureHelp] =
    CompletableFuture.supplyAsync(() => {
      val sh = fragmentAt(params.getTextDocument.getUri, params.getPosition).flatMap { case (gc, sf) =>
        sf match {
          case Application(r: Ref, _) => gc.lookupRef(r)
          case _ => None
        }
      }
      sh match {
        case Some(ed: ExprDecl) =>
          val info = new SignatureInformation(ed.name + ": " + ed.tp.toString)
          val help = new SignatureHelp()
          help.setSignatures(java.util.Collections.singletonList(info))
          help
        case _ => null
      }
    })

  override def documentSymbol(params: DocumentSymbolParams)
      : CompletableFuture[JList[LEither[SymbolInformation, DocumentSymbol]]] =
    CompletableFuture.supplyAsync(() => {
      val uri = params.getTextDocument.getUri
      docs.get(uri) match {
        case None => java.util.Collections.emptyList[LEither[SymbolInformation, DocumentSymbol]]()
        case Some((_, idx)) =>
          val voc = project.get(origin(uri)).getVocabulary
          voc.decls.map(d => LEither.forRight[SymbolInformation, DocumentSymbol](makeSymbol(idx, d))).asJava
      }
    })

  private def makeSymbol(idx: OffsetIndex, decl: Declaration): DocumentSymbol = {
    def range(loc: info.kwarc.p.Location) = {
      val (l1, c1) = idx.toLineCol(loc.from)
      val (l2, c2) = idx.toLineCol(loc.to)
      new Range(new Position(l1, c1), new Position(l2, c2))
    }
    val rg = range(decl.loc)
    decl match {
      case m: Module =>
        val kind = if (m.closed) SymbolKind.Class else SymbolKind.Namespace
        val sym = new DocumentSymbol(m.name, kind, rg, rg)
        sym.setChildren(m.decls.map(d => makeSymbol(idx, d)).asJava)
        sym
      case i: Include =>
        val name = if (i.realize) "realize" else "include"
        new DocumentSymbol(name + " " + i.dom.toString, SymbolKind.Interface, rg, rg)
      case sd: SymbolDeclaration =>
        val detail = sd match {
          case _: TypeDecl => ": type"
          case ed: ExprDecl => ": " + ed.tp.toString
        }
        val sym = new DocumentSymbol(sd.name, SymbolKind.Field, rg, rg)
        sym.setDetail(detail)
        sym
      case other =>
        new DocumentSymbol(other.toString, SymbolKind.Object, rg, rg)
    }
  }
}
