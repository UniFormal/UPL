package info.kwarc.p.lsp

import java.util.concurrent.CompletableFuture

import org.eclipse.lsp4j._
import org.eclipse.lsp4j.services._

import info.kwarc.p.Project

class UplLanguageServer extends LanguageServer with LanguageClientAware {
  // one Project per server process; entries accumulate as files are opened,
  // exactly like VSCodeBridge's `proj` in IDE.scala
  private val project = new Project(Nil)
  private val textDocuments = new UplTextDocumentService(project)
  private val workspace = new UplWorkspaceService

  def connect(client: LanguageClient): Unit = textDocuments.connect(client)

  override def initialize(params: InitializeParams): CompletableFuture[InitializeResult] = {
    val caps = new ServerCapabilities()
    caps.setTextDocumentSync(TextDocumentSyncKind.Full)
    caps.setHoverProvider(true)
    caps.setDefinitionProvider(true)
    caps.setDocumentSymbolProvider(true)
    caps.setCompletionProvider(new CompletionOptions(false, java.util.Collections.singletonList(".")))
    caps.setSignatureHelpProvider(new SignatureHelpOptions(java.util.Collections.singletonList("(")))
    CompletableFuture.completedFuture(new InitializeResult(caps))
  }

  // lsp4j's reflection-based RPC dispatch trips over Scala's mixin forwarder for
  // this interface default method ("Duplicate RPC method initialized") unless
  // it's given an explicit override here.
  override def initialized(params: InitializedParams): Unit = ()

  override def shutdown(): CompletableFuture[Object] = CompletableFuture.completedFuture(null)
  override def exit(): Unit = System.exit(0)

  override def getTextDocumentService: TextDocumentService = textDocuments
  override def getWorkspaceService: WorkspaceService = workspace
}
