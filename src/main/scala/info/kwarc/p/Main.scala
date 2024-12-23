package info.kwarc.p

object Main {
  def main(args: Array[String]): Unit = {
    var left = args.toList
    def next = {val h = left.head; left = left.tail; h}
    val interactive = if (left.headOption contains "--repl") {next; true} else false
    val path = if (left.nonEmpty) File(next) else File("")
    val mn = if (left.nonEmpty) Some(next) else None
    val proj = new Project(path, mn)
    //println(proj)
    proj.process(interactive)
    //println(proj.prog)
  }
}
