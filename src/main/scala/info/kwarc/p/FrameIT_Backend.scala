package info.kwarc.p

import info.kwarc.p.File.{read, readAsSource}

import scala.collection.mutable
import scala.scalajs.js
import js.annotation._
import scala.util.Try

/**
  * A FrameIT SituationTheory (SiTh) is semantically a mutable UPL theory (i.e. a closed [[Module]]),
  * used to store and deduce knowledge about the game-world. In practice, Modules are essentially an immutable
  * `List[Declaration]`, so a [[SiTh_handler]] provides the necessary functionality to pretend access to a
  * mutable [[Module]], while also ensuring nothing contradictory happens when mutating.
  *
  * This is more of an API specification, than an abstraction.
  */
trait SiTh_handler {
  def getSiTh: Module
  def getSiThErrors: List[SError]
  def add(decls_String: String): Boolean
  def add(decls: List[Declaration]): Boolean = add(decls.mkString("\n"))
  def reset(): Unit
  def SiThDecls: List[Declaration]
  //def remove(fact_name: String): Either[List[SError], Module]
  //def eval: TheoryValue
}

/**
  * A FrameIT Project has a "SituationTheory" (SiTh), a UPL theory (i.e. a closed [[Module]]) which can grow over time.
  * This is implemented via a special [[ProjectEntry]]
  * Its current value is accessible via [[getSiTh]], and new declarations can be added via [[add]]
  */
class FrameITProject private()
  extends Project(Nil,None) with SiTh_handler {
  import info.kwarc.p.FrameITProject._
  final val debug: Boolean = false
  entries = List(SiTh)
  main = Option(Parser.expression(SiThOrigin, "SiTh{}", ErrorIgnorer))
  /** The current Situation is always the latest Stage, but with a constant Name ("SiTh") */
  case object SiTh extends ProjectEntry(SiThOrigin) {
    private val proj = FrameITProject.this

    /** Set the SiTh to the combination of all [[Declaration]]s of all SiThFragments */
    def update() = proj.update(SiThOrigin, s"theory SiTh{include ${Stage.current}}")

    def get: Module = getVocabulary
        .decls
        .collectFirst{
          case m: Module if m.name == "SiTh" => m
        }
        .getOrElse { update(); get }

    def decls: List[Declaration] = get.decls
    override def toString: String =
      source.toString ++ " ::" ++ decls.mkString("{\n", "\n", "\n}").indent(1)
  }

  /** Intermediate Stages of the Situation
    * There might be a point in having the Stages encapsulated in their own "Project", the Frame */
  case class Stage(num: Int = Stage.counter) extends ProjectEntry(Stage.Origin(num))
  object Stage {
    var counter = 0
    def current: String = makeName(counter)
    def previous: String = makeName(counter - 1)
    private def makeName(num: Int) = s"Stage$num"
    /** Extractor, because SourceOrigin is a case class and cannot be extended */
    object Origin {
      def apply(num: Int): SourceOrigin = SourceOrigin(makeName(num))

      def unapply(so: SourceOrigin): Option[Int] = so match {
        case SourceOrigin(s"Stage$num", null) => num.toIntOption
        case _ => None
      }
    }
  }

  /** Unlike the content of `BackgroundTheory`, Schemata (formerly Scrolls) operate on the Frame itself,
    * and should thus be first-class citizen of the Project.
    *
    * @todo Actually implement this; The application of a Schema is completely manual rn.
    *       Also add a dedicated SourceOrigin/Extractor then.
    */
  case class SolutionSchema(name: String, dataNeededToGenerateSchemaApplication: Nothing) extends ProjectEntry(SourceOrigin(name)) {
    def apply(stage: Stage, data: Nothing): Stage = ???
  }

  /** Helper Entry for the application of a Schema. For now it's easiest to just keep them around. */
  case class SchemaApplication(num: Int) extends ProjectEntry(SchemaApplication.Origin(num))
  object SchemaApplication {
    var counter = 0
    def next: (SourceOrigin, String) = {
      counter += 1
      (Origin(counter), makeName(counter))
    }
    private def makeName(num: Int) = s"Application$num"
    /** Extractor, because SourceOrigin is a case class and cannot be extended */
    object Origin {
      def apply(id: Int = counter): SourceOrigin = SourceOrigin(makeName(id))

      def unapply(so: SourceOrigin): Option[Int] = so match {
        case SourceOrigin(s"Application$num", null) => num.toIntOption
        case _ => None
      }
    }
  }

  def SiThDecls = SiTh.decls
  def getSiTh = SiTh.get

  def add(decls_String: String): Boolean = {
    Stage.counter += 1
    val stageString = s"theory ${Stage.current}{include ${Stage.previous} $decls_String}"
    updateAndCheck(Stage.Origin(Stage.counter), stageString)
    SiTh.update()
    if (debug) println(check(SiThOrigin, false))
    checkErrors()
  }

  def applySchema(schema: String, requiredFacts: List[(String,String)], acquiredFacts: List[(String,String)]) = {
    val (apOrigin,apName) = SchemaApplication.next
    val reqDecls = requiredFacts map {case (n, d) => s"$n = $d"} mkString " "
    val apCode = s"theory t$apName{include ${Stage.current} realize $schema $reqDecls} $apName = t$apName{}"
    updateAndCheck(apOrigin,apCode)
    val accDecls = acquiredFacts map {case (n, d) => s"$n = $apName.$d"} mkString " "
    add(accDecls)
  }

  def reset(): Unit = {
    Stage.counter = 0
    entries = entries.filterNot(e => e.isInstanceOf[Stage] || e.isInstanceOf[SchemaApplication])
    SiTh.update()
  }
  def getSiThErrors: List[SError] = SiTh.errors.getErrors

  /** Find the corresponding [[ProjectEntry]] in [[entries]].
    *
    * If there isn't one yet, create it, and insert it as the __second to last__ entry, before the [[SiTh]]
    */
  override def get(so: SourceOrigin): ProjectEntry = entries.find(_.source == so).getOrElse {
    val e = so match {
      case Stage.Origin(n) => Stage(n)
      case SchemaApplication.Origin(n) => SchemaApplication(n)
      case _ => new ProjectEntry(so)
    }
    entries = entries match {
      case es :+ sith => es :+ e :+ sith
      case _ => e :: Nil
    }
    e
  }
  def tryEval(input: String) = {
    Try{
      val parsed = Parser.expression(SourceOrigin.anonymous, input, ErrorThrower)
      val voc = check(true)
      val (checked, _) = ThrowingChecker.checkAndInferExpression(GlobalContext(voc), parsed)
      val (_, r) = Interpreter.run(Program(voc, checked))
      r
    }
  }

  def checkAll()= {
    val (dirty,checked) = entries.view.filter(_.global).partition(_.checkedIsDirty)
    val voc: mutable.Queue[Declaration] = mutable.Queue.from(checked.flatMap(_.checked.decls))
    dirty.foreach{ le =>
      if(!le.errors.hasErrors) {
        val ch = new Checker(le.errors)
        le.checked = ch.checkVocabulary(GlobalContext(voc), le.parsed, true)(le.parsed)
        le.checkedIsDirty = false
      }
      voc ++= le.getVocabulary.decls
    }
    TheoryValue(voc.toList)
  }
  def debugPrintVerbose(): Unit = println (entries.map(_.getVocabulary).mkString("\n"))
}

object FrameITProject {
  // SiTh: SituationTheory
  private val SiThOrigin: SourceOrigin = SourceOrigin("SiTh")

  /**
    * Create a FrameIT project from an unfolded UPL project-file
    * Using LazyLists means we don't need to keep all file contents in Memory.
    *
    * This implementation avoids using files explicitly, so it can be exported via scala.js
    *
    * @param fileContents An unfolded UPL project-file (*.pp)
    *                     Relevant keys:
    *   - "background" (or "source") files are considered background and all content is added to the project as is
    *   - "schemata" ToDo Extract required and acquired facts from Schemata.
    *   - "stageInit" the first listed file is used as content for [[FrameITProject.Stage]]0. All others are ignored
    * @return A fully set up FrameIt project
    */
  def apply(fileContents: Map[String, LazyList[(SourceOrigin, String)]]): FrameITProject = {
    val saveFileContents =  fileContents.withDefaultValue(LazyList.empty)
    val sourceKinds = List("background", "source", "schemata").view // List because we need the order for `entries`
    val entries = for {
      k <- sourceKinds
      (source, content) <- saveFileContents(k)
    } yield ProjectEntry(source, content)
    val project = new FrameITProject()
    project.entries = entries ++: project.entries // prepend the background, SiTh remains last element
    val siO = for {
      l <- fileContents get "stageInit"
      (_ , c) <- l.headOption
    } yield c
    val stageInitCode = s"theory ${project.Stage.current}{${siO.getOrElse("")}}"
    project.update(SourceOrigin("InitialStage"), stageInitCode)
    project.checkAll()
    project
  }

  /** Convenience method for providing a single background, ect. in code  */
  def apply(backgroundContent: String, schemataContent:String, initialStageContent:String=""): FrameITProject = {
    val contents: Map[String, LazyList[(SourceOrigin, String)]] = Map(
      ("background", LazyList((SourceOrigin("Background"), backgroundContent))),
      ("schemata",   LazyList((SourceOrigin("Background"), schemataContent))),
      ("stageInit",  LazyList((SourceOrigin("InitialStage"), initialStageContent)))
    )
    FrameITProject(contents)
  }

  /**
    * Create a FrameIT project from a UPL project-file (*.pp)
    *
    * Relevant properties:
    *  - "background" (or "source") files are considered background and all content is added to the project as is
    *  - "schemata" ToDo Extract required and acquired facts from Schemata.
    *  - "stageInit" the first listed file is used as content for [[FrameITProject.Stage]]0. All others are ignored
    *
    * @param setupFile A UPL project-file (*.pp)
    * @return A fully set up FrameIt project
    */
  def apply(setupFile: File): FrameITProject = FrameITProject(unfoldProjectFile(setupFile))


  /** Kinda chimera of [[File.readPropertiesFromString]] and [[Project.fromFile]],
    * because both aren't quite flexible enough to be used here.  */
  protected def unfoldProjectFile(projFile: File): Map[String, LazyList[(SourceOrigin, String)]] = {
    if (!(projFile.getExtension contains "pp")) {
      return Map(("background", LazyList.from(Project.pFiles(projFile).map(readAsSource))))
    }
    val r = scala.io.Source.fromFile(projFile.toJava)
    val props = new mutable.HashMap[String, LazyList[(SourceOrigin, String)]].withDefaultValue(LazyList.empty)
    r.getLines()
      .map(_.strip())
      .filter(!_.startsWith("//"))
      .foreach { line =>
        val p +: v = LazyList from line.split(":", 2)
        if (p.nonEmpty && v.nonEmpty) { // make sure line contains colon and the key is non-empty
          val key = p.strip()
          val value = v
            .flatMap(_.split("\\s"))
            .filter(_.nonEmpty)
            .flatMap(s => Project.pFiles(projFile.up.resolve(s)))
            .map{f => readAsSource(f)}
          props.updateWith(key) {
            case None => Option(value)
            case Some(old) => Option(old #::: value)
          }
        }
      }
    props.map{ case (k, v) => (k,v) }.toMap
  }
}

/**
  * The API for interfacing with the UPL Situation Theory from the outside.
  * Hides all the fancy Scala stuff [[SiTh_handler]] can use, and instead provides simple return types.
  *
  * (Currently, the only expected "outside" is JS)
  */
@JSExportTopLevel("FrameIT")
@JSExportAll
object FrameIT_Backend {
  import Gameplay._
  implicit val debug: Boolean = false
  private var proj = FrameITProject("","")

  def main(args: Array[String]): Unit = {
    gameplayTest()
  }

  /** private, so scala.js doesn't need to see [[File]] */
  private def gameplayTest() = {
    proj = FrameITProject(File("test/FrameIt/Gameplay_Example/gameplay.pp"))
    //proj add s1
    proj applySchema("_SimilarTriangles", assignments, List(("height", "__EA"))) // ("height_P","__EA_P") doesn't work
    println(proj.tryEval("SiTh{}.height"))

  }

  // ToDO: Make a useful JS Object
  def makeJSReadable(declaration: Declaration) = declaration.toString

  def showSiTh: String = proj.getSiTh.toString

  def getSiThErrors: String = proj.getSiThErrors.mkString("\n")

  /** Add [[Declaration]]s to the SiTh
    *
    * @param decls_String The declarations to add, as raw code string
    * @return True if no error occurred, false otherwise.
    */
  def add(decls_String: String): Boolean = proj.add(decls_String)

  def resetLevel(): Unit = proj.reset()

  def newLevel(backgroundTheoryContent: String, schemataContent:String): Unit =
  { proj = FrameITProject(backgroundTheoryContent, schemataContent) }

  @JSExport("eval")
  def JS_eval(exprS: String): String = {
    val ts = proj.tryEval(exprS)
    //ts.fold(err => err.toString, expression => expression.toString)
    ts.toString
  }
}

object Gameplay{
  /** The Background */
  val bg =
    """type point
      |type triangle = (point,point,point)
      |dist: point -> point -> float
      |similar: triangle -> triangle -> bool
      |theory _SimilarTriangles{
      |  _A: point _B: point _C: point _D: point _E: point
      |  _CD: float _CD_P:  |- dist(_C)(_D) == _CD
      |  _CE: float _CE_P:  |- dist(_C)(_E) == _CE
      |  _DB: float _DB_P: |- dist(_D)(_B) == _DB
      |  _are_similar: |- similar((_A,_C,_E))((_B,_C,_D))
      |  __EA = _CE * _DB / _CD __EA_P: |- dist(_E)(_A) == __EA = ???
      |}""".stripMargin

  val s1 =
    """tip: point = ???
      |foot: point = ??? ground: point = ??? p: point = ??? q: point = ???
      |ground_dist_small = 42 ground_dist_small_P:  |- dist(ground)(q) == ground_dist_small = ???
      |ground_dist_large = 420 ground_dist_large_P:  |- dist(ground)(foot) == ground_dist_large = ???
      |apparent_height = 42 apparent_height_P: |- dist(q)(p) == apparent_height = ???
      |are_similar: |- similar((tip,ground,foot))((p, ground, q)) = ???""".stripMargin

  val assignments = List(
    ("_A", "tip"), ("_B", "p"), ("_C", "ground"), ("_D", "q"), ("_E", "foot"),
    ("_CD", "ground_dist_small"), ("_CD_P", "ground_dist_small_P"),
    ("_CE", "ground_dist_large"), ("_CE_P", "ground_dist_large_P"),
    ("_DB", "apparent_height"), ("_DB_P", "apparent_height_P"),
    ("_are_similar", "are_similar"))

  val s2 =
    """realize _SimilarTriangles
      |_A = tip _B = p _C = ground _D = q _E = foot
      |_CD = ground_dist_small _CD_P = ground_dist_small_P
      |_CE = ground_dist_large _CE_P = ground_dist_large_P
      |_DB = apparent_height _DB_P = apparent_height_P
      |_are_similar = are_similar""".stripMargin
}

/** Experimental factory to make common, but convoluted, declarations easier to interact with.*/
object ValueFact {
  ////// Useful conversions.
  import scala.language.implicitConversions
  implicit def varDeclAsDecl(expr: EVarDecl): ExprDecl = expr match {
    case EVarDecl(name, tp, dfO, mutable, output) => ExprDecl(name, LocalContext.empty, tp, dfO, None, Modifiers(false, mutable))
  }
  implicit def exprDeclAsExpr(decl: ExprDecl): EVarDecl = decl match {
    case ed: ExprDecl => EVarDecl(ed.name, ed.tp, ed.dfO, ed.modifiers.mutable)
  }
  //////

  def apply(name: String, func: ClosedRef, args: List[Expression], value: Double): ExprDecl = {
    val tp = ProofType(Equality(
      positive = true,
      tp = NumberType.Float,
      left = Application(func, args),
      right = FloatValue(value)
    ))
    val modifiers = Modifiers(closed = false, mutable = false)
    //VarDecl(name, tp, dfO = None, mutable = false)
    ExprDecl(name, LocalContext.empty, tp, dfO = None, None, modifiers)
  }

  def unapply(decl: ExprDecl): Option[(ClosedRef, List[Expression], Double)] = {
    decl.tp match {
      case ProofType(Equality(true, NumberType.Float, Application(fun: ClosedRef, args), FloatValue(value))) =>
        Some(fun, args, value)
      case _ => None
    }
  }
}