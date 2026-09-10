package info.kwarc.p.lsp

import org.eclipse.lsp4j._
import org.eclipse.lsp4j.services.WorkspaceService

/** UPL has no cross-file workspace-wide requests yet (no rename, no
  * workspace symbol search); this just satisfies the LSP lifecycle
  * notifications so clients don't error out.
  */
class UplWorkspaceService extends WorkspaceService {
  override def didChangeConfiguration(params: DidChangeConfigurationParams): Unit = ()
  override def didChangeWatchedFiles(params: DidChangeWatchedFilesParams): Unit = ()
}
