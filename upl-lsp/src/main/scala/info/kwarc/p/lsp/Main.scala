package info.kwarc.p.lsp

import org.eclipse.lsp4j.launch.LSPLauncher

/** Entry point for the standalone UPL language server: a plain JVM process
  * speaking LSP over stdio, no Node/VS Code involved. Point any generic LSP
  * client (eglot, lsp-mode, coc.nvim, ...) at:
  *
  *   java -jar upl-lsp.jar
  */
object Main {
  def main(args: Array[String]): Unit = {
    val server = new UplLanguageServer()
    val launcher = LSPLauncher.createServerLauncher(server, System.in, System.out)
    server.connect(launcher.getRemoteProxy)
    launcher.startListening()
  }
}
