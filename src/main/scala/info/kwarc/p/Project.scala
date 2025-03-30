package info.kwarc.p

/**
  * a part in a project with mutable fields maintained by the project
  */
class ProjectEntry(val source: SourceOrigin) {
  /** A source part may be split into fragments, e.g., for notebook cells.
    * Such documents can see the global ones but not each other.
    */
  def global = source.fragment == null
  var parsed: Vocabulary = Vocabulary.empty
  var checked: Vocabulary = Vocabulary.empty
  var checkedIsDirty = false
  var result: Vocabulary = Vocabulary.empty
  var errors = new ErrorCollector
  def getVocabulary = if (checkedIsDirty) parsed else checked
}

/**
  * A project stores interrelated toplevel source snippets.
  * @param entries the sources
  * @param main the main call to run this project
  */
class Project(private var entries: List[ProjectEntry], main: Option[Expression] = None) {
  override def toString = entries.map(_.source.toString).mkString(", ") + ": " + main.getOrElse("(no main)")
  def get(so: SourceOrigin) = entries.find(_.source == so).getOrElse {
    val e = new ProjectEntry(so)
    entries = entries ::: List(e)
    e
  }

  def hasErrors = entries.exists(_.errors.hasErrors)
  def getErrors = entries.flatMap(_.errors.getErrors)

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
    (Vocabulary(gs:::lesC),Vocabulary(gs:::lesR))
  }
  /** all global entries concatenated */
  def makeGlobalContext() = {
    val ds = entries.filter(_.global).flatMap(_.getVocabulary.decls)
    Vocabulary(ds).toGlobalContext
  }

  def update(so: SourceOrigin, src: String) = {
    val le = get(so)
    le.errors.clear
    le.parsed = Parser.text(so, src, le.errors)
    le.checkedIsDirty = true
  }

  def check(so: SourceOrigin, alsoRun: Boolean): Vocabulary = {
    val le = get(so)
    val (vocC,vocR) = makeGlobalContext(so)
    if (le.checkedIsDirty) {
      if (le.errors.hasErrors) return le.parsed
      val ch = new Checker(le.errors)
      val leC = ch.checkVocabulary(vocC.toGlobalContext,le.parsed,true)(le.parsed)
      le.checked = leC
      le.checkedIsDirty = false
    }
    if (alsoRun) {
      if (le.errors.hasErrors) return le.checked
      val ip = new Interpreter(vocR)
      val leR = le.checked.decls.map(ip.interpretDeclaration(_))
      le.result = Vocabulary(leR)
      le.result
    } else {
      le.checked
    }
  }

  def check(stopOnError: Boolean) = {
    val ds = entries.flatMap(_.parsed.decls)
    val voc = Vocabulary(ds)
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

  def run(): Option[Interpreter] = {
    val voc = check(true)
    if (hasErrors) {
      println(getErrors.mkString("\n"))
      return None
    }
    val e = main.getOrElse(UnitValue)
    val ch = new Checker(ErrorThrower)
    try {
      val (eC,_) = ch.checkAndInferExpression(GlobalContext(voc), e)
      val prog = Program(voc,eC)
      val (ip,r) = Interpreter.run(prog)
      if (r != UnitValue) println(r)
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
      result = ed.toString
      if (ec.hasErrors) {
        result += ec
      } else {
        try {
          val edI = ip.interpretDeclaration(ed)
          result += edI
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
    while (true) {
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
  def fromFile(projFile: File, main: Option[String] = None): Project = {
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
    val mainE = mainS.map(s => Parser.expression(projFile.toSourceOrigin, s, ErrorThrower))
    val es = paths.map {p =>
      new ProjectEntry(p.toSourceOrigin)
    }
    val p = new Project(es,mainE)
    p.entries.foreach {e => p.update(e.source, Parser.getFileContent(File(e.source.toString)))}
    p
  }

}