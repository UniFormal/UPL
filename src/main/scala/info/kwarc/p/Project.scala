package info.kwarc.p

class ProjectEntry(val source: SourceOrigin) {
  var parsed: Vocabulary = Vocabulary.empty
  var checked: Vocabulary = Vocabulary.empty
  var checkedIsDirty = false
  var errors: List[PError] = Nil
}

class Project(var entries: List[ProjectEntry], main: Option[Expression] = None) {
  override def toString = entries.map(_.source.toString).mkString(", ") + ": " + main.getOrElse("(no main)")
  def get(so: SourceOrigin) = entries.find(_.source == so).getOrElse {
    val e = new ProjectEntry(so)
    entries = entries ::: List(e)
    e
  }

  private def makeGlobalContext(so: SourceOrigin) = {
    val ds = entries.takeWhile(_.source != so).flatMap(_.checked.decls)
    GlobalContext(Module.anonymous(ds))
  }

  def update(so: SourceOrigin, src: String) = {
    val le = get(so)
    le.errors = Nil
    le.parsed = try {
      Parser.text(so, src)
    } catch {
      case e: PError => le.errors = List(e); Vocabulary.empty
    }
    le.checkedIsDirty = true
  }
  def check(so: SourceOrigin): Unit = {
    val le = get(so)
    if (!le.checkedIsDirty) return
    val gc = makeGlobalContext(so)
    val vocC = try {
      Checker.checkVocabulary(gc, le.parsed, true)(le.parsed)
    } catch {
      case e: PError => le.errors ::= e; le.parsed
    }
    le.checked = vocC
  }

  def check() = {
    val ds = entries.flatMap(_.parsed.decls)
    val voc = Vocabulary(ds)
    Checker.checkVocabulary(GlobalContext(""), voc, true)(voc)
  }

  def run(interactive: Boolean) = {
    val voc = check()
    val e = main.getOrElse(UnitValue)
    val (eC,_) = Checker.inferExpression(GlobalContext(voc), e)
    val prog = Program(voc, eC)
    val (ip,r) = Interpreter.run(prog)
    if (r != UnitValue) println(e)
    if (interactive) repl(ip)
  }

  def repl(ip: Interpreter): Unit = {
    var i = 0
    val so = SourceOrigin("shell")
    while (true) {
      val s = scala.io.StdIn.readLine()
      if (s == "exit") return
      val e = Parser.expression(so,s)
      val (eC,eI) = Checker.inferExpression(GlobalContext(ip.voc),e)
      val ed = ExprDecl("res" + i.toString,eI,Some(eC),false)
      i += 1
      println(ed)
      val edI = ip.interpretDeclaration(ed)
      println(edI)
    }
  }
}

/**
  * @param projFile either a .pp file containing a project description or a source file/folder
  * @param main the expression to run
  *
  * A .pp file is of the form (key:value)^* where the keys are
  * - source: a list of source files/folders (may occur multiple times)
  * - main: the main expression
  */
object Project {
  private def pFiles(f: File) = f.descendants.filter(_.getExtension contains "p")
  def fromFile(projFile: File, main: Option[String] = None) = {
    val (paths,mainS) = if (projFile.getExtension contains "pp") {
      val props = File.readPropertiesFromString(File.read(projFile))
      val src = props.get("source").getOrElse("").split("\\s")
      val mn = props.get("main")
      val ps = src.toList.flatMap {s =>
        val f = projFile.up.resolve(s)
        pFiles(f)
      }
      (ps, mn)
    } else {
      (pFiles(projFile), main)
    }
    val mainE = mainS.map(s => Parser.expression(projFile.toSourceOrigin, s))
    val es = paths.map {p =>
      new ProjectEntry(p.toSourceOrigin)
    }
    val p = new Project(es,mainE)
    p.entries.foreach {e => p.update(e.source, File.read(File(e.source.toString)))}
    p
  }
}