package info.kwarc.p

/**
  * a part in a project with mutable fields maintained by the project
  */
class ProjectEntry(val source: SourceOrigin) {
  /** A source part may be split into fragments, e.g., for notebook cells.
    * Such documents can see the global ones but not each other.
    */
  def global = source.fragment == null
  var parsed = Theory.empty
  var checked = Theory.empty
  var checkedIsDirty = false
  var result = Theory.empty
  var errors = new ErrorCollector

  override def toString = s"$source:$getVocabulary"

  def getVocabulary = if (checkedIsDirty) parsed else checked
}

/**
  * A project stores interrelated toplevel source snippets.
  */
class MultiFileProject() {


  /** the main call to run this project */
  var main: Option[Expression] = None
  protected var entries: List[ProjectEntry] = Nil
  override def toString: String = entries.map(_.source.toString).mkString(", ") + ": " + main.getOrElse("(no main)")
  def verboseToString: String = entries.map(_.toString).mkString("\n") + "\nmain: " + main.getOrElse("()")

  def get(so: SourceOrigin): ProjectEntry = entries.find(_.source == so).getOrElse {
    val e = new ProjectEntry(so)
    entries = entries ::: List(e)
    e
  }

  def hasErrors: Boolean = entries.exists(_.errors.hasErrors)
  def getErrors: List[SError] = entries.flatMap(_.errors.getErrors)

  def fragmentAt(loc: Location)= {
    val gc = makeGlobalContext()
    val pe = get(loc.origin)
    val voc = pe.getVocabulary
    voc.descendantAt(gc,loc)
  }

  /** all global entries concatenated except for the given document; checked resp. executed */
  def makeGlobalContext(so: SourceOrigin) = {
    val gs = entries.filter(e => e.global && e.source.path != so.path).flatMap(_.checked.decls)
    val les = entries.filter(e => !e.global && e.source.path == so.path && e.source.fragment != so.fragment)
    val lesC = les.flatMap(_.checked.decls)
    val lesR = les.flatMap(_.result.decls)
    (TheoryValue(gs:::lesC),TheoryValue(gs:::lesR))
  }
  /** all global entries concatenated */
  def makeGlobalContext(): GlobalContext = {
    val ds = entries.filter(_.global).flatMap(_.getVocabulary.decls)
    GlobalContext(TheoryValue(ds))
  }

  def update(so: SourceOrigin, src: String): Unit = {
    val le = get(so)
    le.errors.clear
    le.parsed = Parser.text(so, src, le.errors)
    le.checkedIsDirty = true
  }

  def check(so: SourceOrigin, alsoRun: Boolean = false): TheoryValue = {
    val le = get(so)
    val (vocC,vocR) = makeGlobalContext(so)
    if (le.checkedIsDirty) {
      if (le.errors.hasErrors) return le.parsed
      val ch = new Checker(le.errors)
      val leC = ch.checkVocabulary(GlobalContext(vocC),le.parsed,true)(le.parsed)
      le.checked = leC
      le.checkedIsDirty = false
    }
    if (alsoRun) {
      if (le.errors.hasErrors) return le.checked
      val ip = new Interpreter(vocR)
      val leR = le.checked.decls.map(ip.interpretDeclaration)
      le.result = TheoryValue(leR)
      le.result
    } else {
      le.checked
    }
  }

  def check(stopOnError: Boolean): TheoryValue = {
    val ds = entries.flatMap(_.parsed.decls)
    val voc = TheoryValue(ds)
    val ec = if (stopOnError) ErrorThrower else new ErrorCollector
    val ch = new Checker(ec)
    val vocC = ch.checkVocabulary(GlobalContext(""), voc, true)(voc)
    ec match {
      case ec: ErrorCollector =>
        ec.getErrors.groupBy(e => e.loc.origin).foreach {case (o,es) =>
          val eh = get(o).errors
          es foreach eh.apply
        }
      case _ =>
    }
    vocC
  }

  def checkErrors(): Boolean = {
    if (hasErrors) {
      println(getErrors.mkString("\n"))
      true
    } else
      false
  }

  def run(): Option[Interpreter] = {
    if (checkErrors()) return None
    val voc = check(true)
    if (checkErrors()) return None
    val e = main.getOrElse(UnitValue)
    val ch = new Checker(ErrorThrower)
    try {
      val (eC,_) = ch.checkAndInferExpression(GlobalContext(voc), e)
      val prog = Program(voc,eC)
      val (ip,r) = Interpreter.run(prog)
      println(r)
      Some(ip)
    } catch {
      case e: PError =>
        println(e)
        None
    }
  }

  def replLine(ip: Interpreter, id: Int, input: String): String = {
    val so = SourceOrigin("shell")
    val ec = new ErrorCollector
    val e = Parser.expression(so,input,ec)
    if (ec.hasErrors) {
      ec.getErrors.mkString("\n")
    } else {
      var result = ""
      val ec = new ErrorCollector
      val ch = new Checker(ec)
      val (eC,eI) = ch.checkAndInferExpression(GlobalContext(ip.voc),e)
      val ed = ExprDecl("res" + id.toString,eI,Some(eC),false)
      result = ed.toString + "\n"
      if (ec.hasErrors) {
        result += ec
      } else {
        try {
          val edI = ip.interpretDeclaration(ed)
          result = edI.dfO.getOrElse("").toString
        } catch {
          case e: PError =>
            result += e.toString
        }
      }
      result
    }
  }

  def repl(ip: Interpreter): Unit = {
    var i = 0
    println("Welcome to the UPL REPL\ntype 'exit' to leave")
    while (true) {
      print("> ")
      val s = scala.io.StdIn.readLine()
      if (s == "exit") return
      i += 1
      val result = replLine(ip, i, s)
      println(result)
    }
  }
  def runMaybeRepl(dropToRepl: Boolean): Unit = {
    val ipO = run()
    if (dropToRepl) ipO foreach {ip => repl(ip)}
  }
}

object MultiFileProject {
  private val fileEndings = List(".p", ".p.tex")
  private def pFiles(f: File) = {
    val candidates = if (f.toJava.isFile) List(f) else f.descendants
    candidates.filter(d => fileEndings.exists(d.getName.endsWith))
  }

  /**
    * @param projFile either a .pp file containing a project description or a source file/folder
    * @param main     the expression to run
    *
    * @note           A .pp file is of the form (key:value)^*^ where the keys are
    *                 - source: a list of source files/folders (may occur multiple times)
    *                 - main: the main expression
    */
  def fromFile(projFile: File, main: Option[String] = None): MultiFileProject = {
    val (paths,mainS) = if (projFile.getExtension contains "pp") {
      val props = File.readPropertiesFromString(File.read(projFile))
      val src = props.getOrElse("source", "").split("\\s")
      val mn = props.get("main")
      val ps = src.toList.flatMap {s =>
        val f = projFile.up.resolve(s)
        pFiles(f)
      }
      (ps, mn)
    } else {
      (pFiles(projFile), main)
    }
    val p = new MultiFileProject()
    p.main = mainS.map(s => Parser.expression(projFile.toSourceOrigin, s, ErrorThrower))
    for (file <- paths) {
      p.update(file.toSourceOrigin, Parser.getFileContent(file))
      // new ProjectEntry(file.toSourceOrigin)
    }
    // p.entries.foreach {e => p.update(e.source, Parser.getFileContent(File(e.source.toString)))}
    p
  }

}