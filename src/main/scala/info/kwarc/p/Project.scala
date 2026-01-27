package info.kwarc.p


/** A part in a project with mutable fields maintained by the projects */
class ProjectEntry(val source: SourceOrigin) {
  override def toString: String = source.toString
  val errors = new ErrorCollector
  val depInter = new DependencyInterface
  var parsed = Theory.empty
  var checked = Theory.empty
  var checkedIsDirty = false
  var result = Theory.empty
  def global = source.fragment == null
  def getVocabulary = if (checkedIsDirty) parsed else checked
}

/**
 * A project stores interrelated toplevel source snippets.
 * @param main the main call to run this project
 */
class Project(protected var entries: List[ProjectEntry], var main: Option[Expression] = None) {
  override def toString: String = entries.map(_.source).mkString(", ") + ": " + main.getOrElse("(no main)")

  // holds errors with unknown location
  val errors = new ErrorCollector

  def get(so: SourceOrigin) = entries.find(_.source == so).getOrElse {
    val e = new ProjectEntry(so)
    entries = entries ::: List(e)
    e
  }
  def hasErrors: Boolean = errors.hasErrors || entries.exists(_.errors.hasErrors)
  def getErrors: List[SError] = errors.getErrors ::: entries.flatMap(_.errors.getErrors)
  private def getErrorContainer(soO: Option[SourceOrigin]) = soO match {
    case None => errors
    case Some(o) => get(o).errors
  }

  def fragmentAt(loc: Location) = {
    val gc = makeGlobalContext()
    val pe = get(loc.origin)
    val voc = pe.getVocabulary
    voc.descendantAt(gc,loc)
  }

  /** all entries concatenated except for the given document; checked resp. executed */
  def makeGlobalContext(so: SourceOrigin) = {
    val gs = entries.filter(e => e.global && e.source.container != so.container).flatMap(_.checked.decls)
    val les = entries.filter(e => !e.global && e.source.container == so.container && e.source.fragment != so.fragment)
    val lesC = les.flatMap(_.checked.decls)
    val lesR = les.flatMap(_.result.decls)
    (TheoryValue(gs ::: lesC),TheoryValue(gs ::: lesR))
  }

  /** all global entries concatenated */
  def makeGlobalContext() = {
    val ds = entries.filter(_.global).flatMap(_.getVocabulary.decls)
    GlobalContext(ds)
  }

  def update(so: SourceOrigin, src: String) = {
    val le = get(so)
    le.errors.clear
    le.parsed = Parser.text(so, src, le.errors)
    // the following line can be used during debugging to find missing locations in parsed content
    // TestLocationFields(Module.anonymous(le.parsed.decls))(GlobalContext(le.parsed.decls),())
    DependencyAnalyzer.update(le)
    le.checkedIsDirty = true
  }

  def updateAndCheck(so: SourceOrigin, src: String): TheoryValue = {
    try{
      update(so, src)
      check(so, false).approximateMissingLocations()
    }
    catch{
      case _: PError => get(so).getVocabulary
    }

  }

  def check(so: SourceOrigin, alsoRun: Boolean): TheoryValue = {
    val le = get(so)
    val (vocC,vocR) = makeGlobalContext(so)
    if (le.checkedIsDirty) {
      if (le.errors.hasErrors) return le.parsed
      val ch = new Checker(le.errors)
      val leC = ch.checkVocabulary(GlobalContext(vocC), le.parsed, true)(le.parsed)
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

  def check(stopOnError: Boolean) = {
    val ds = entries.flatMap(_.parsed.decls)
    val voc = TheoryValue(ds)
    val ec = if (stopOnError) ErrorThrower else new ErrorCollector
    val ch = new Checker(ec)
    val vocC = ch.checkVocabulary(GlobalContext(""), voc, true)(voc)
    ec match {
      case ec: ErrorCollector =>
        errors.clear
        ec.getErrors.groupBy(e => Option(e.loc).map(_.origin)).foreach {case (o,es) =>
          val eh = getErrorContainer(o)
          eh.clear
          es foreach eh.apply
        }
      case _ =>
    }
    vocC
  }

  def checkErrors() = {
    if (hasErrors) {
      println(getErrors.mkString("\n"))
      true
    } else
      false
  }

  /** initialize and run 'main' */
  def run(): Option[Interpreter] = {
    if (checkErrors()) return None
    val voc = check(false)
    if (checkErrors()) return None
    val e = main.getOrElse(UnitValue)
    val ch = new Checker(ErrorThrower)
    try {
      val (eC, _) = ch.checkAndInferExpression(GlobalContext(voc), e)
      val prog = Program(voc, eC)
      val (ip, r) = Interpreter.run(prog)
      println(r)
      Some(ip)
    } catch {
      case e: PError =>
        println(e)
        None
    }
  }

  def repl(ip: Interpreter): Unit = {
    println("Welcome to the UPL REPL\ntype 'exit' to leave")
    var i = 0
    val ec = new ErrorCollector
    val ch = new Checker(ec)
    var gc = GlobalContext(ip.voc)
    while (true) {scala.io.StdIn.readLine("> ") match {
      case "exit" => return
      case "#context" => println(gc)
      case input =>
        i += 1
        val so = SourceOrigin.shell(i)
        ec.clear
        val e = Parser.expression(so, input, ec)
        val output = if (ec.hasErrors) {
          ec.getErrors.mkString("\n")
        } else {
          var result = ""
          val (eC, eI) = ch.checkAndInferExpression(gc, e)
          val vd: EVarDecl = eC match {
            case v: EVarDecl => v
            case e => EVarDecl("res" + i.toString, eI, Some(eC), true, false)
          }
          gc = gc.append(LocalContext.collectContext(vd))
          result = vd.toString
          if (ec.hasErrors) {
            result += "\n" + ec
          } else {
            try {
              val vdI = ip.interpretExpression(vd)
              result += "\n --> " + vdI
            } catch {
              case e: PError =>
                result += "\n" + e.toString
            }
          }
          result
        }
        println(output)
      }
    }
  }

  /** evaluates [[main]] and starts a REPL afterwards, returns true if so
    */
  def runMaybeRepl(dropToRepl: Boolean): Unit = {
    val ipO = run()
    if (dropToRepl) ipO foreach {ip => repl(ip)}
  }
}

object Project {
  private val fileEndings = List(".p", ".p.tex")
  private def pFiles(f: File) = {
    val candidates = if (f.toJava.isFile) List(f) else f.descendants
    candidates.filter(d => fileEndings.exists(d.getName.endsWith))
  }

  /**
    * @param projFile either a .pp file containing a project description or a source file/folder
    * @param main     the expression to run
    * A .pp file is of the form (key:value)^*^ where the keys are
    * - source: a list of source files/folders (may occur multiple times)
    * - main: the main expression
    */
  def fromFile(projFile: File, main: Option[String] = None): Project = {
    val (paths,mainS) = if (projFile.getExtension contains "pp") {
      val props = File.readPropertiesFromString(File.read(projFile))
      val src = props("source").getOrElse("").split("\\s")
      val mn = props("main")
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

object ProjectTest{
  val testCode: String = "val t = 1 match{n}"
  def main(args: Array[String]): Unit = {
    val proj = new Project(Nil)
    proj.updateAndCheck(SourceOrigin("Test"), testCode)
    proj.checkErrors()
    proj.runMaybeRepl(true)
  }
}
