package info.kwarc.p


/** A part in a project with mutable fields maintained by the project
  * @todo [[Project]] has several methods where every other line starts with `entry.`
  *       I suggest we move [[ProjectEntry]] into Project, and those methods into [[ProjectEntry]].
  */
class ProjectEntry(val source:SourceOrigin) {

  var parsed = Theory.empty
  var checked = Theory.empty
  var checkedIsDirty = false
  var result = Theory.empty
  var errors = new ErrorCollector
  def getVocabulary = if (checkedIsDirty) parsed else checked

  override def toString: String = source.toString ++ ":\n" ++ getVocabulary.toString.indent(2)
}

/**
 * A project stores interrelated toplevel source snippets.
 * @param main the main call to run this project
 */
class Project(main: Option[Expression] = None) {
  protected var entries: List[ProjectEntry] = Nil
  override def toString: String =
    entries.map(_.source).mkString(", ") + ": " + main.getOrElse("(no main)")

  def verboseToString: String =
    entries.mkString("\n") + "\nmain: " + main.getOrElse("()")

  def get(so: SourceOrigin) = entries.find(_.source == so).getOrElse {
    val e = new ProjectEntry(so)
    entries = entries :+ e
    e
  }
  def hasErrors: Boolean = entries.exists( _.errors.hasErrors )
  def getErrors: List[SError] = entries.flatMap(_.errors.getErrors)

  def fragmentAt(loc: Location) = {
    val gc = makeGlobalContext()
    val pe = get(loc.origin)
    val voc = pe.getVocabulary
    voc.descendantAt(gc,loc)
  }

  def isInContext(other: SourceOrigin)(implicit so: SourceOrigin) = {
    so != other && (global(other) || so.container == other.container)
  }

  def global(so: SourceOrigin) = so.fragment == null

  /** all global entries concatenated except for the given document; checked resp. executed */
  def makeContexts(implicit so: SourceOrigin) = {
    val (checked, results) = (for {
      e <- entries
      s = e.source
      r = e.result.decls
      c = e.checked.decls
      if isInContext(s)
    } yield {
      if (s.isStandalone) (c,c)
      else (c,r)
    }).unzip
    (GlobalContext(checked.flatten), TheoryValue(results.flatten))

      // The old semantic, for comparison
//    val es = entries.filter(isInContext)
//    val gs = es.filter(_.source.isStandalone).flatMap(_.checked.decls)
//    val les = es.filter(!_.source.isStandalone)
//    val lesC = les.flatMap(_.checked.decls)
//    val lesR = les.flatMap(_.result.decls)
//    (GlobalContext((gs ++ lesC).toList), TheoryValue((gs ++ lesR).toList))
  }

  /** all global entries concatenated */
  def makeGlobalContext() = {
    val ds = for {
      e <- entries
      if global(e.source)
      decl <- e.getVocabulary.decls
    } yield decl
    GlobalContext(ds)
  }

  def shallowUpdate(so: SourceOrigin, src: String) = {
    val le = get(so)
    le.errors.clear
    le.parsed = Parser.text(so, src, le.errors)
    le.checkedIsDirty = true
  }

  def update(so: SourceOrigin, src: String) = {
    shallowUpdate(so, src)
    runChecker(so)
  }

  def runChecker(so: SourceOrigin, gc: Option[GlobalContext] = None): Unit = {
    val le = get(so)
    if (le.checkedIsDirty) {
      if (le.errors.hasErrors) return
      val vocC = gc.getOrElse(makeContexts(so)._1)
      val ch = new Checker(le.errors)
      val leC = ch.checkVocabulary(vocC, le.parsed, true)(le.parsed)
      le.checked = leC
      le.checkedIsDirty = false
    }
  }

  def checkAndRun(so: SourceOrigin): TheoryValue = {
    val le = get(so)
    if (le.errors.hasErrors)
      return { if (le.checkedIsDirty) le.parsed else le.checked }
    val (vocC,vocR) = makeContexts(so)
    runChecker(so, Some(vocC))
    if (le.errors.hasErrors)
      return le.checked
    val ip = new Interpreter(vocR)
    val leR = le.checked.decls.map(ip.interpretDeclaration)
    le.result = TheoryValue(leR)
    le.result
  }

  def checkAll(throwOnError: Boolean) = {
    val ds = entries.flatMap(_.getVocabulary.decls)
    val voc = TheoryValue(ds)
    val ec = if (throwOnError) ErrorThrower else new ErrorCollector
    val ch = new Checker(ec)
    val vocC = ch.checkVocabulary(GlobalContext(""), voc, true)(voc)
    ec match {
      case ec: ErrorCollector =>
        ec.getErrors.groupBy(e => e.loc.origin).foreach {case (o,es) =>
          val eh = get(o).errors
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

  def run(): Option[Interpreter] = {
    if (checkErrors()) return None
    val voc = checkAll(false)
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

  def repl(ip: Interpreter): Unit = {
    println("Welcome to the UPL REPL\ntype 'exit' to leave")
    var i = 0
    val ec = new ErrorCollector
    val ch = new Checker(ec)
    var gc = GlobalContext(ip.voc)
    while (true) {
      print("> ")
      val input = scala.io.StdIn.readLine()
      if (input == "exit") return
      i += 1
      val so = SourceOrigin.shell(i)
      val e = Parser.expression(so,input,ec)
      val output = if (ec.hasErrors) {
        ec.getErrors.mkString("\n")
      } else {
        var result = ""
        val (eC,eI) = ch.checkAndInferExpression(gc,e)
        gc = gc.append(LocalContext.collectContext(eC))
        val ed = ExprDecl("res" + i.toString,eI,Some(eC),false)
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
      println(output)
    }
  }

  /** Attempts to evaluate [[main]], and start a REPL afterwards
    *
    * @return
    *  - `true` if the REPL successfully started (and closed)
    *  - `false` if an error occurred, and the REPL couldn't start
    */
  def tryStartRepl(): Boolean = {
    run() match {
      case Some(ip) => repl(ip); true
      case None => false
    }
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
    *
    *                 A .pp file is of the form (key:value)^*^ where the keys are
    *                 - source: a list of source files/folders (may occur multiple times)
    *                 - main: the main expression
    */
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
    val proj = new Project(mainE)
    paths.foreach { file =>
      proj.shallowUpdate(file.toSourceOrigin, Parser.getFileContent(file))
    }
    proj
  }

}