package info.kwarc.p

import scala.collection.mutable
import scala.collection.MapView

/** A part in a project with mutable fields maintained by the project
  * @todo ProjectEntries currently serve two purposes:
  *       - parsed, checked, result and getVocabulary are the internal representation of a piece of source code
  *       - source, inContextFor, checkedIsDirty and shallowUpdate serve the management of that code in the project
  *       only `errors` serves both purposes, and both times it's a "nice-to-have".
  *       I suggest making "CodeEntry", or "SourceContent" (mirroring [[SourceOrigin]]) its own thing.
  *       [[Parser]], [[Checker]] and [[Interpreter]] may prefer to use them, over [[TheoryValue]]s with social contracts.
  *       ---
  *       As a first step I removed the use of [[ProjectEntry.source]] from [[Project]]
  */
class ProjectEntry(source:SourceOrigin) {

  var parsed = Theory.empty
  var checked = Theory.empty
  var checkedIsDirty = false
  var result = Theory.empty
  var errors = new ErrorCollector

  def getVocabulary: TheoryValue = if (checkedIsDirty) parsed else checked

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

/**
  * A project stores interrelated source snippets.
  * @todo Currently [[Project]] implicitly assumes to be a [[MultiSourceProject]],
  *       although it's intended to become more general.
  * @todo There may be a point in having [[Project]] extend [[mutable.Map]][ [[SourceOrigin]], ???]
  *       (for some sensible pick of ???), because it kind of is mostly an extension of its `entries` field
  */
trait Project{
  /** the main call to run this project */
  var main: Option[Expression] = None
  /** the entries of the project.  */
  protected var entries: mutable.Map[SourceOrigin, ProjectEntry] = mutable.Map.empty

  override def toString: String =
    entries.keysIterator.mkString(", ") + ": " + main.getOrElse("(no main)")

  def verboseToString: String =
    entries.mkString("\n") + "\nmain: " + main.getOrElse("()")

  def get(so: SourceOrigin): ProjectEntry = {
    entries.getOrElseUpdate(so, new ProjectEntry(so))
  }

  def hasErrors: Boolean = entries.valuesIterator.exists( _.errors.hasErrors )

  def getErrors: List[SError] = entries.valuesIterator.flatMap(_.errors.getErrors).toList

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
    val declsInContext = entries.view
      .filterKeys(_.inContextFor(so))
      .mapValues(_.checked.decls)
      .values.flatten
    GlobalContext(declsInContext)
  }

  /** all visible entries concatenated except for the given document; checked resp. executed
    *
    * @return All global declarations, and the evaluation of all other fragments in the same source
    *
    * @todo Is the order of sources of relevance here? The current implementation guarantees NO order, but
    *       there is a snippet below that does some grouping
    */
  def makeEvaluationContext(so: SourceOrigin): TheoryValue = {
    val decls = entries.view
      .collect {
        case (_: GlobalSource, e) => e.checked.decls
        case (oso, e) if oso.inContextFor(so) => e.result.decls
      }.flatten.toList
    TheoryValue(decls)

//    val (lRs, gCs) = entries.view
//      .filterKeys(_.inContextFor(so))
//      .partitionMap{
//        case (_: SourceFragment,e) => Left(e.result.decls)
//        case (_,e) => Right(e.checked.decls)
//      }
//    TheoryValue((gCs ++ lRs).flatten.toList)
  }

  /** all global entries concatenated */
  def makeGlobalContext(): GlobalContext = {
    val ds = entries.view.collect{ case (_: GlobalSource,e) => e.getVocabulary.decls }.flatten
    GlobalContext(ds)
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

  /**
    * @todo There is no canonical way to handle non-global [[SourceOrigin]]s in the returned [[TheoryValue]].
    *       I will just ignore them outright, but that means they will not be checked, despite the name of this method
    * @return
    */
  def checkProject(): Either[List[SError], TheoryValue] = {
    val ds = entries.view
      .collect{case (_:GlobalSource, e) => e.parsed.decls}
      .flatten.toList
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
    *  - `true` if the REPL successfully started (and closed)
    *  - `false` if an error occurred, and the REPL couldn't start
    */
  def tryStartRepl(): Boolean = {
    run() match {
      case Some(ip) => repl(ip); true
      case None     => false
    }
  }
}


/**
  * A multi-source project contains code from multiple (truly independent) sources, e.g.
  */
class MultiSourceProject() extends Project

object MultiSourceProject {
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
  def fromFile(projFile: File, main: Option[String] = None): MultiSourceProject = {
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
    val p = new MultiSourceProject()
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
