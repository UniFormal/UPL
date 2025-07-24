package info.kwarc.p

//<editor-fold desc="SourceOrigin">
/**
  * An abstraction of source files
  *  - avoids dependency on java.io.File
  *  - allows representation of non-file sources, like
  *   - notebook cells
  *   - REPL inputs
  *   - the FrameIT SituationTheory
  */
sealed trait SourceOrigin{
  /**
    * Toplevel declarations of a global source are in the context for all other sources
    * Non global sources may override [[inContextFor]] to give visibility conditions
    */
  def global: Boolean
  /** Are the toplevel declarations in this source visible from the other Source? */
  def inContextFor(other: SourceOrigin): Boolean = global && this != other
}
/** An independent Source; toplevel declarations are globally visible
  * @example Files
  * @param source an identifier of this source, such as a file path or URL
  */
case class StandaloneSource(source: String) extends SourceOrigin {
  def global: Boolean = true
  override def toString: String = source
}
/** A small code fragment; toplevel declarations are visible only for other fragments of the same source
  * @example Cells of a notebook-file
  * @param source an identifier shared by all fragments of the same source, such as a file path or URL
  * @param fragment an identifier of the fragment
  */
case class SourceFragment(source: String, fragment: String) extends SourceOrigin {
  def global: Boolean = false
  override def toString: String = source + "#" + fragment

  override def inContextFor(other: SourceOrigin): Boolean = other match {
    case SourceFragment(otherSource, otherFragment)
      if otherSource == source && otherFragment != fragment => true
    case _ => false
  }
}
/** An anonymous source, behaves like a [[StandaloneSource]], but is guaranteed to always be unique.
  * @example inputs to an interactive Interpreter
  */
final case class AnonymousSource private (id: Int) extends SourceOrigin {
  def global: Boolean = true
  override def toString: String = s"??$id"
}
object AnonymousSource{
  def global: Boolean = false
  private var counter = -1
  /**  */
  private def apply(id: Int): AnonymousSource = {
    counter += 1
    new AnonymousSource(counter)
  }

  def getNew(): AnonymousSource = {
    counter += 1
    new AnonymousSource(counter)
  }
}
/** TmpSource is a volatile Source, that (semantically) is not actually stored.
  * Its declarations are not visible to any other Source, and a [[ProjectEntry]]([[TmpSource]])
  * can be overwritten without consequences.
  * @example - parse/check/evaluate some input, without affecting the project
  *          - REPL lines
  */
case object TmpSource extends SourceOrigin{
  def global: Boolean = false
  override def inContextFor(other: SourceOrigin): Boolean = false
}
//</editor-fold>

trait Project {

  /** A part in a project with mutable fields maintained by the project */
  protected class ProjectEntry(val source: SourceOrigin) {
  /**
    * Global entries are visible to all others
    */
  def global: Boolean = source.global

  /** Are the toplevel declarations in this entry in the context for the other Source? */
  def inContextFor(so: SourceOrigin): Boolean = source.inContextFor(so)

  var parsed = Theory.empty
  var checked = Theory.empty
  var checkedIsDirty = false
  var result = Theory.empty
  var errors = new ErrorCollector

  override def toString = s"$source:$getVocabulary"

  def getVocabulary: TheoryValue = if (checkedIsDirty) parsed else checked

  def getStatus: Either[List[SError], TheoryValue] = {
    if (errors.hasErrors) Left(errors.getErrors)
    else Right(getVocabulary)
  }

  /** Updates this entry with new code, without type-checking.
    * Doesn't throw on parser errors, but set [[errors]] instead.
    *
    * @param src The new code as [[String]], to be parsed.
    */
  def shallowUpdate(src: String) = {
    errors.clear
    parsed = Parser.text(source, src, errors)
    checkedIsDirty = true
  }

  /** Updates this entry, without type-checking.
    *
    * @param thVal the new value of this.[[parsed]]
    */
  def shallowUpdate(thVal: TheoryValue) = {
    parsed = thVal
    errors.clear
    checkedIsDirty = true
  }
}

  /** the main call to run this project */
  var main: Option[Expression] = None
  protected var entries: List[ProjectEntry] = Nil

  override def toString: String =
    entries.map(_.source.toString).mkString(", ") + ": " + main.getOrElse(
      "(no main)"
    )

  def verboseToString: String =
    entries.map(_.toString).mkString("\n") + "\nmain: " + main.getOrElse("()")

  def get(so: SourceOrigin): ProjectEntry =
    entries.find(_.source == so).getOrElse {
      val e = new ProjectEntry(so)
      entries = entries ::: List(e)
      e
    }

  def hasErrors: Boolean = entries.exists(_.errors.hasErrors)

  def getErrors: List[SError] = entries.flatMap(_.errors.getErrors)

  def fragmentAt(loc: Location) = {
    val gc = makeGlobalContext()
    val pe = get(loc.origin)
    val voc = pe.getVocabulary
    voc.descendantAt(gc, loc)
  }

  /** All visible entries concatenated except for the given document
    *
    * @return All declarations that are in the context for checking `so`
    */
  def makeContext(so: SourceOrigin): GlobalContext = {
    val declsInContext = entries
      .filter(_.inContextFor(so))
      .flatMap(_.checked.decls)
    GlobalContext(TheoryValue(declsInContext))
  }

  /** all visible entries concatenated except for the given document; checked resp. executed
    *
    * @return All global declarations, and the evaluation of all other fragments in the same source
    */
  def makeEvaluationContext(so: SourceOrigin): TheoryValue = {
    val (gEs, lEs) = entries
      .filter(_.inContextFor(so))
      .partition(_.source match {
        case _: SourceFragment => false
        case _                 => true
      })
    val gCs = gEs.flatMap(_.checked.decls)
    val lRs = lEs.flatMap(_.result.decls)
    TheoryValue(gCs ::: lRs)
  }

  /** all global entries concatenated */
  def makeGlobalContext(): GlobalContext = {
    val ds = entries.filter(_.global).flatMap(_.getVocabulary.decls)
    GlobalContext(TheoryValue(ds))
  }

  def check(so: SourceOrigin): Either[List[SError], TheoryValue] = {
    val le = get(so)
    val gc = makeContext(so)
    if (le.checkedIsDirty) {
      if (le.errors.hasErrors) return Left(le.errors.getErrors)
      val ch = new Checker(le.errors)
      try {
        val leC = ch.checkVocabulary(gc, le.parsed, true)(le.parsed)
        le.checked = leC
        le.checkedIsDirty = false
      } catch {
        case _: PError => return Left(le.errors.getErrors)
      }
    }
    Right(le.checked)
  }

  def checkAndRun(so: SourceOrigin): Either[List[PError], TheoryValue] = {
    val le = get(so)
    val vocR = makeEvaluationContext(so)
    val checkedOrError = check(so)
    checkedOrError.flatMap { checked =>
      val ip = new Interpreter(vocR)
      try {
        val leR = checked.decls.map(ip.interpretDeclaration)
        le.result = TheoryValue(leR)
        Right(le.result)
      } catch {
        case err: PError => Left(List(err))
      }
    }
  }

  /** Updates the entry for `so`, or creates one if no such entry exists yet
    *
    * @param so  The [[SourceOrigin]] of the code
    * @param src The code as [[String]]
    * @return Either
    *         - Left: The list of errors encountered while parsing/checking
    *         - Right: The parsed and checked theory
    */
  def update(
              so: SourceOrigin,
              src: String
            ): Either[List[SError], TheoryValue] = {
    val le = get(so)
    le.shallowUpdate(src)
    check(so)
  }

  /** Updates the entry for `so`, or creates one if no such entry exists yet
    *
    * @param so  The [[SourceOrigin]] of the code
    * @param thVal The already parsed code as [[TheoryValue]]
    * @return Either
    *         - Left: The list of errors encountered while parsing/checking
    *         - Right: The parsed and checked theory
    */
  def update(
              so: SourceOrigin,
              thVal: TheoryValue
            ): Either[List[SError], TheoryValue] = {
    val le = get(so)
    le.shallowUpdate(thVal)
    check(so)
  }

  def checkProject(): Either[List[SError], TheoryValue] = {
    val ds = entries.flatMap(_.parsed.decls)
    val voc = TheoryValue(ds)
    val ec = new ErrorCollector
    val ch = new Checker(ec)
    val vocC = ch.checkVocabulary(GlobalContext(""), voc, true)(voc)
    if (ec.hasErrors) {
      ec.getErrors.groupBy(e => e.loc.origin).foreach { case (o, es) =>
        val eh = get(o).errors
        es foreach eh.apply
      }
      Left(ec.getErrors)
    } else Right(vocC)
  }

  def run(): Option[Interpreter] = {
    val voc = checkProject() match {
      case Left(errs) =>
        println(errs.mkString("\n"))
        return None
      case Right(voc) => voc
    }
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

  protected def replLine(ip: Interpreter, id: Int, input: String): String = {
    val ec = new ErrorCollector
    val e = Parser.expression(TmpSource, input, ec)
    if (ec.hasErrors) {
      ec.getErrors.mkString("\n")
    } else {
      var result = ""
      val ec = new ErrorCollector
      val ch = new Checker(ec)
      val (eC, eI) = ch.checkAndInferExpression(GlobalContext(ip.voc), e)
      val ed = ExprDecl("res" + id.toString, eI, Some(eC), false)
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

  /** Attempts to evaluate [[main]], and start a REPL afterwards
    *
    * @return
    *  - true if the REPL successfully started (and closed)
    *  - false if an error occurred, and the REPL couldn't start
    */
  def tryStartRepl(): Boolean = {
    run() match {
      case Some(ip) => repl(ip); true
      case None     => false
    }
  }
}

/**
  * A project stores interrelated toplevel source snippets.
  */
class MultiFileProject() extends Project

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
      p
        .get(file.toSourceOrigin) // new ProjectEntry(file.toSourceOrigin)
        .shallowUpdate(Parser.getFileContent(file))
    }
    // p.entries.foreach {e => p.update(e.source, Parser.getFileContent(File(e.source.toString)))}
    p
  }
}

}