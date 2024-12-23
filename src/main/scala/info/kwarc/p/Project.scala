package info.kwarc.p

/**
  * @param projFile either a .pp file containing a project description or a source file/folder
  * @param main the expression to run
  *
  * A .pp file is of the form (key:value)^* where the keys are
  * - source: a list of source files/folders (may occur multiple times)
  * - main: the main expression
  */
class Project(projFile: File, var main: Option[String] = None) {
  private val ephemeral = !(projFile.getExtension contains "pp")
  private var paths: List[File] = if (ephemeral) List(projFile) else Nil
  private var prog: Program = Program(Nil,UnitValue)

  override def toString = (if (ephemeral) "ephemeral " else "") + "project of " + projFile

  private def effectiveDeclarations(d: Declaration): List[Declaration] = d match {
    case m: Module if m.anonymous => m.decls.flatMap(effectiveDeclarations)
    case _ => List(d)
  }

  def load(): Unit = {
    if (ephemeral) return
    val props = File.readPropertiesFromString(File.read(projFile))
    val src = props.get("source").getOrElse("").split("\\s")
    paths = src.map(projFile.up.resolve).toList
    main = props.get("main")
  }

  def parse() = {
    val files = paths.flatMap(f => f.descendants.filter(_.getExtension contains "p"))
    val mods = files.map(Parser.file)
    val decls = effectiveDeclarations(Module.anonymous(mods))
    val e = main.map(s => Parser.expression("main",s)).getOrElse(UnitValue)
    prog = Program(decls,e)
  }

  def check() = {
    val pC = Checker.checkProgram(prog)
    prog = pC
  }

  def run() = {
    val (ip,e) = Interpreter.run(prog)
    if (e != UnitValue) println(e)
    ip
  }

  def process(interactive: Boolean) = {
    load()
    parse()
    check()
    val ip = run()
    if (interactive) repl(ip)
  }

  def repl(ip: Interpreter) = {
    var i = 0
    while (true) {
      val s = scala.io.StdIn.readLine()
      val e = Parser.expression("shell",s)
      val (eC,eI) = Checker.inferExpression(GlobalContext(ip.voc),e)
      val ed = ExprDecl("res" + i.toString,eI,Some(eC),false)
      i += 1
      println(ed)
      val edI = ip.interpretDeclaration(ed)
      println(edI)
    }
  }
}