package info.kwarc.p

class ProjectEntry(val source: SourceOrigin) {
  var parsed: Vocabulary = Vocabulary.empty
  var checked: Vocabulary = Vocabulary.empty
  def getVocabulary = if (checkedIsDirty) parsed else checked
  var checkedIsDirty = false
  var errors = new ErrorCollector
}

class Project(var entries: List[ProjectEntry], main: Option[Expression] = None) {
  override def toString = entries.map(_.source.toString).mkString(", ") + ": " + main.getOrElse("(no main)")
  def get(so: SourceOrigin) = entries.find(_.source == so).getOrElse {
    val e = new ProjectEntry(so)
    entries = entries ::: List(e)
    e
  }

  def hasErrors = entries.exists(_.errors.hasErrors)
  def getErrors = entries.flatMap(_.errors.getErrors)

  def makeGlobalContext(so: SourceOrigin) = {
    val ds = entries.takeWhile(_.source != so).flatMap(_.checked.decls)
    GlobalContext(Module.anonymous(ds))
  }
  def makeGlobalContext() = {
    val ds = entries.flatMap(_.getVocabulary.decls)
    GlobalContext(Module.anonymous(ds))
  }

  def update(so: SourceOrigin, src: String) = {
    val le = get(so)
    le.errors.clear
    le.parsed = Parser.text(so, src, le.errors)
    le.checkedIsDirty = true
  }
  def check(so: SourceOrigin): Unit = {
    val le = get(so)
    if (!le.checkedIsDirty) return
    val gc = makeGlobalContext(so)
    val ch = new Checker(le.errors)
    val vocC = ch.checkVocabulary(gc, le.parsed, true)(le.parsed)
    le.checked = vocC
    le.checkedIsDirty = false
  }

  def check() = {
    val ds = entries.flatMap(_.parsed.decls)
    val voc = Vocabulary(ds)
    val ec = new ErrorCollector
    val ch = new Checker(ec)
    val vocC = ch.checkVocabulary(GlobalContext(""), voc, true)(voc)
    ec.getErrors.groupBy(e => e.loc.origin).foreach {case (o, es) =>
      val eh = get(o).errors
      es foreach eh.apply
    }
    vocC
  }

  def run(interactive: Boolean): Unit = {
    val voc = check()
    if (hasErrors) {
      println(getErrors.mkString("\n"))
      return
    }
    val e = main.getOrElse(UnitValue)
    val ec = new ErrorCollector
    val ch = new Checker(ec)
    val (eC,_) = ch.inferExpression(GlobalContext(voc), e)
    if (ec.hasErrors) {
      println(ec)
    } else {
      val prog = Program(voc,eC)
      try {
        val (ip,r) = Interpreter.run(prog)
        if (r != UnitValue) println(r)
        if (interactive) repl(ip)
      } catch {
        case e: PError => println(e)
      }
    }
  }

  def repl(ip: Interpreter): Unit = {
    var i = 0
    val so = SourceOrigin("shell")
    while (true) {
      val s = scala.io.StdIn.readLine()
      if (s == "exit") return
      val ec = new ErrorCollector
      val e = Parser.expression(so,s,ec)
      if (ec.hasErrors) {
        println(ec.getErrors.mkString("\n"))
      } else {
        val ec = new ErrorCollector
        val ch = new Checker(ec)
        val (eC,eI) = ch.inferExpression(GlobalContext(ip.voc),e)
        val ed = ExprDecl("res" + i.toString,eI,Some(eC),false)
        i += 1
        println(ed)
        if (ec.hasErrors) {
          println(ec)
        } else {
          try {
            val edI = ip.interpretDeclaration(ed)
            println(edI)
          } catch {case e: PError =>
            println(e)
          }
        }
      }
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
  private val fileEndings = List(".p", ".p.tex")
  private def pFiles(f: File) = f.descendants.filter(d => fileEndings.exists(d.getName.endsWith))
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
    val mainE = mainS.map(s => Parser.expression(projFile.toSourceOrigin, s, ErrorThrower))
    val es = paths.map {p =>
      new ProjectEntry(p.toSourceOrigin)
    }
    val p = new Project(es,mainE)
    p.entries.foreach {e => p.update(e.source, Parser.getFileContent(File(e.source.toString)))}
    p
  }
}