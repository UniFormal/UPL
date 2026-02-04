package info.kwarc.p

import scala.scalajs.js.annotation._
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
class FrameITProject private(main: Option[Expression] = None)(implicit debug: Boolean)
  extends Project(Nil, main) with SiTh_handler {
  import info.kwarc.p.FrameITProject._
  /** The current Situation is always the latest Stage, but with a constant Name ("SiTh") */
  case object SiTh extends ProjectEntry(SiThOrigin) {
    private val proj = FrameITProject.this

    /** Set the SiTh to the combination of all [[Declaration]]s of all SiThFragments */
    def update() = proj.update(SiThOrigin, s"theory SiTh{include ${Stage.current}}")

    /** May be useful in a future where the Stages can split */
    private def updateAsCombination(frags: List[Int]) = {
      val includes = for (f <- frags) yield s"include ${fragment(f)}"
      updateAndCheck(SiThOrigin, s"theory SiTh{${includes.mkString(" ")}}")
    }

    def get: Module =
      getVocabulary
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
    def current: String = s"Stage$counter"
    def previous: String = s"Stage${counter-1}"
    /** Extractor, because SourceOrigin is a case class and cannot be extended */
    object Origin {
      def apply(id: Int): SourceOrigin = SourceOrigin("SiTh", id.toString)
      def unapply(so: SourceOrigin): Option[Int] = so match {
        case SourceOrigin("SiTh", id) => id.toIntOption
        case _ => None
      }
    }
  }
  /** Unlike the content of `BackgroundTheory`, Schemata (formerly Scrolls) operate on the Frame itself,
    * and should thus be first-class citizen of the Project.
    *
    * @todo Actually implement this; The application of a Scheme is completely manual rn.
    *       Also add a dedicated SourceOrigin/Extractor then.
    */
  case class SolutionScheme(name: String, dataNeededToGenerateSchemeApplication: Any) extends ProjectEntry(SourceOrigin(name))
  /** Helper Entry for the application of a Scheme */
  case class SchemeApplication(num: Int) extends ProjectEntry(SchemeApplication.Origin(num))
  object SchemeApplication {
    private var counter = 0
    /** Extractor, because SourceOrigin is a case class and cannot be extended */
    object Origin {
      def next: SourceOrigin = {
        counter += 1
        SourceOrigin("Application", counter.toString)
      }
      def apply(id: Int): SourceOrigin = SourceOrigin("Application", id.toString)
      def unapply(so: SourceOrigin): Option[Int] = so match {
        case SourceOrigin("Application", id) => id.toIntOption
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

  def applyScheme(scheme: String, apDeclsS: String, solDeclsS: String) = {
    val apOrigin = SchemeApplication.Origin.next
    val apCode = s"theory $apOrigin{include ${Stage.current} realize $scheme $apDeclsS}"
    updateAndCheck(apOrigin,apCode)
    add(solDeclsS)
  }

  def reset(): Unit = {
    Stage.counter = 0
    entries = entries.filterNot(e => e.isInstanceOf[Stage] || e.isInstanceOf[SchemeApplication])
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
      case SchemeApplication.Origin(n) => SchemeApplication(n)
      case _ => new ProjectEntry(so)
    }
    entries = entries match {
      case es :+ sith => es :+ e :+ sith
      case _ => e :: Nil
    }
    e
  }
  def tryReadAndRun(input: String) = {
    Try{
      val parsed = Parser.expression(SourceOrigin.anonymous, input, ErrorThrower)
      val voc = check(true)
      val (checked, _) = ThrowingChecker.checkAndInferExpression(GlobalContext(voc), parsed)
      val (_, r) = Interpreter.run(Program(voc, checked))
      r
    }
  }
}

object FrameITProject{
  // SiTh: SituationTheory
  private val SiThOrigin: SourceOrigin = SourceOrigin("SiTh")
  def apply(backgroundTheoryContent: String, initialStageContent:String="", main: String = "")(implicit debug: Boolean): FrameITProject = {
    val btOrigin = SourceOrigin("BackgroundTheory")
    val mainE = Try(Parser.expression(SiThOrigin, main, ErrorThrower)).toOption
    val proj = new FrameITProject(mainE)
    proj.entries = List[ProjectEntry](new ProjectEntry(btOrigin), proj.SiTh)

    // Add the BackgroundTheory. Compare [[proj.tryAdd]]
    val btString = s"$backgroundTheoryContent " + // The actual Background
      s"theory ${proj.Stage.current}{$initialStageContent}" // The initial Stage. Won't be deleted by [[reset]]
    proj.updateAndCheck(btOrigin, btString)
    proj
  }
  private def fragment(i: Int) = s"Stage$i"
}

object Gameplay{
  def test() = {
    val proj = FrameITProject(bg)(false)
    proj add s1
    proj add s2
    println(proj.tryReadAndRun("SiTh{}.__EA"))
  }
  /** The Background */
  val bg =
    """type point
      |type triangle = (point,point,point)
      |dist: point -> point -> float
      |similar: triangle -> triangle -> bool
      |theory _simTri_Scroll{
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
      |apparent_height = 21 apparent_height_P: |- dist(q)(p) == apparent_height = ???
      |are_similar: |- similar((tip,ground,foot))((p, ground, q)) = ???""".stripMargin

  val s2 =
    """realize _simTri_Scroll
      |_A = tip _B = p _C = ground _D = q _E = foot
      |_CD = ground_dist_small _CD_P = ground_dist_small_P
      |_CE = ground_dist_large _CE_P = ground_dist_large_P
      |_DB = apparent_height _DB_P = apparent_height_P
      |_are_similar = are_similar""".stripMargin
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
  implicit val debug: Boolean = false
  private var proj = FrameITProject("")

  def main(args: Array[String]): Unit = {
    Gameplay.test()
  }

  // ToDO: Make a useful JS Object
  def makeJSReadable(declaration: Declaration) = declaration.toString

  @JSExport("showSiTh")
  def JS_showSiTh: String = proj.getSiTh.toString

  @JSExport("SiThErrors")
  def JS_getSiThErrors: String = proj.getSiThErrors.mkString("\n")

  /** Add [[Declaration]]s to the SiTh
    *
    * @param decls_String The declarations to add, as raw code string
    * @return True if no error occurred, false otherwise.
    */
  @JSExport("tryAdd")
  def JS_addS(decls_String: String): Boolean = proj.add(decls_String)

  def resetLevel(): Unit = proj.reset()

  @JSExport("newLevel")
  def JS_newProject(backgroundTheoryContent: String): Unit = { proj = FrameITProject(backgroundTheoryContent) }

  @JSExport("eval")
  def JS_eval(exprS: String): String = {
    val ts = proj.tryReadAndRun(exprS)
    //ts.fold(err => err.toString, expression => expression.toString)
    ts.toString
  }
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