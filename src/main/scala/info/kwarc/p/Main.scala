package info.kwarc.p

object Main {
  def main(args: Array[String]): Unit = {
    var left = args.toList
    if (args.isEmpty) {println(doc); return}
    def next = {val h = left.head; left = left.tail; h}
    val interactive = if (left.headOption contains "--repl") {next; true} else false
    val path = if (left.nonEmpty) File(next) else File(".")
    val mn = if (left.nonEmpty) Some(next) else None
    val proj = Project.fromFile(path, mn)
    //println(proj)
    proj.run(interactive)
  }

  val doc =
"""[--repl] PATH [EXPR]
where
PATH: project file or source file/folder
EXPR: toplevel call relative to sources
--repl: drop into REPL after running ('exit' to quit)
"""
}
