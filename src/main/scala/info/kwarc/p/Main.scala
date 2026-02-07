package info.kwarc.p

object Main {
  def main(args: Array[String]): Unit = {
    var left = args.toList
    if (args.isEmpty) {println(doc); return}
    def next = {val h = left.head; left = left.tail; h}
    val isabelle = if (left.headOption contains "--isabelle") {next; true} else false
    val interactive = if (left.headOption contains "--repl"){next; true} else false
    val path = if (left.nonEmpty) File(next) else File(".")
    val mn = if (left.nonEmpty) Some(next) else None
    val proj = Project.fromFile(path, mn)
    //println(proj)
    if (isabelle) Project.toIsabelleFiles(proj) else proj.runMaybeRepl(interactive)
  }

  val doc =
    """[--repl/--isabelle] PATH1 [PATH2] [EXPR]
    where
    PATH1: project file or source file/folder
    PATH2: target folder for isabelle files
    EXPR: toplevel call relative to sources
    --repl: drop into REPL after running ('exit' to quit)
    --isabelle: translate to Isabelle code (and evaluate main expression with 'value')
    """

}