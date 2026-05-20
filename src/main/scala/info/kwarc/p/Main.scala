package info.kwarc.p

object Main {
  def main(args: Array[String]): Unit = {
    val (mainArgs, progArgs) =
      args.span(_ != "--") match {
        case (a, Array()) => (a, Array.empty[String])
        case (a, b)       => (a, b.tail)
      }

    var left = mainArgs.toList
    if (args.isEmpty) {println(doc); return}
    def next = {val h = left.head; left = left.tail; h}
    val isabelle = if (left.headOption contains "--isabelle") {next; true} else false
    val interactive = if (left.headOption contains "--repl"){next; true} else false
    val path = if (left.nonEmpty) File(next) else File(".")
    val mn = if (left.nonEmpty) Some(next) else None
    val proj = Project.fromFile(path, mn)
    //println(proj)
    if (isabelle) Project.toIsabelleFiles(proj) else proj.runMaybeRepl(interactive, progArgs.toList)
  }

  val doc =
    """[--repl/--isabelle] PATH [EXPR] [-- PROGRAM_ARGS...]
    where
    PATH: project file or source file/folder
    EXPR: toplevel call relative to sources
    PROGRAM_ARGS: arguments to the program (can be accessed with 'args' in the main expression)
    --repl: drop into REPL after running ('exit' to quit)
    --isabelle: translate to Isabelle code and write to file(s) in same location
    """

}