package info.kwarc.p

import scala.collection.SeqMap
import scala.scalajs.js
import js.annotation._

/**
  * The API for interfacing with the Backend from the outside.
  * Hides all the fancy Scala and UPL stuff [[FrameITProject]] can use, and instead provides simple return types.
  *
  * (Currently, the only expected "outside" is JS)
  */
@JSExportTopLevel("FrameIT")
@JSExportAll
object FrameIT_Backend {
  import Gameplay._
  implicit val debug: Boolean = false
  var proj = FrameITProject("","")

  def main(args: Array[String]): Unit = {
    gameplayTest()
  }

  /** private, so scala.js doesn't need to see [[File]] */
  private def gameplayTest() = {
    //proj = FrameITProject(File("test/FrameIt/Gameplay_Example/gameplay.pp"))
    newLevel(bg,schema)
    add(s1)
    proj applySchema("_SimilarTriangles", assignments, SeqMap(("height", "__CD"))) // ("height_P","__CD_P") doesn't work right now
    println(proj.tryEval("SiTh{}.height"))
    debugPrintVerbose()

  }

  // ToDO: Make a useful JS Object
  def makeJSReadable(declaration: Declaration) = declaration.toString

  def showSiTh: String = proj.SiTh.get.toString

  def getSiThErrors: String = proj.getSiThErrors.mkString("\n")
  def getErrors = proj.getErrors.mkString("\n")

  /** Add [[Declaration]]s to the SiTh
    *
    * @param decls_String The declarations to add, as raw code string
    * @return `true` if no error occurred, `false` otherwise.
    * @example {{{
    *          if(add("i:int")) showSiTh
    *          else getErrors}}}
    */
  def add(decls_String: String): Boolean = proj.Stage.add(decls_String)

  def resetLevel(): Unit = proj.reset()

  def newLevel(backgroundTheoryContent: String, schemataContent: String): Boolean = {
    proj = FrameITProject(backgroundTheoryContent, schemataContent)
    !proj.hasErrors
  }

  @JSExport("eval")
  def JS_eval(exprS: String): js.Object = {
    val triedExpression = proj.tryEval(exprS)
    new js.Object {
      val success = triedExpression.isSuccess
      val content = triedExpression.fold(_.toString,_.toString)
    }
  }

  /** @see [[FrameITProject.applySchema]]
    *
    */
  def applySchema (schema:String, assignReq:js.Dictionary[String], assignRes:js.Dictionary[String])= {
    proj.applySchema(schema, assignReq, assignRes)
  }

  def debugPrintVerbose() = proj.debugPrintVerbose()
}

object Gameplay{
  /** The Background
    *
    * FrameIT.newLevel("type point type triangle = (point,point,point) dist: point -> point -> float similar: triangle -> triangle -> bool", "theory _SimilarTriangles{ _A: point   _B: point  _C: point  _D: point  _E: point _AB: float  _AB_P:  |- dist(_A)(_B) == _AB _AC: float  _AC_P:  |- dist(_A)(_C) == _AC _BE: float  _BE_P: |- dist(_B)(_E) == _BE _are_similar: |- similar((_D,_A,_C))((_E,_A,_B)) __CD = _AC * _BE / _AB  __CD_P: |- dist(_C)(_D) == __CD = ???}")
    */
  val bg =
    """type point
      |type triangle = (point,point,point)
      |dist: point -> point -> float
      |similar: triangle -> triangle -> bool
      |""".stripMargin

  /** The used Schema */
  val schema =
    """theory _SimilarTriangles{
      |  _A: point   _B: point  _C: point  _D: point  _E: point
      |  _AB: float  _AB_P:  |- dist(_A)(_B) == _AB
      |  _AC: float  _AC_P:  |- dist(_A)(_C) == _AC
      |  _BE: float  _BE_P: |- dist(_B)(_E) == _BE
      |  _are_similar: |- similar((_D,_A,_C))((_E,_A,_B))
      |  __CD = _AC * _BE / _AB  __CD_P: |- dist(_C)(_D) == __CD = ???
      |}""".stripMargin
  val jsSchemaApp =
    """assign = new Map()
      |tmp = [["_A", "ground"], ["_B", "q"], ["_C", "foot"], ["_D", "tip"], ["_E", "p"],
      |["_AB", "ground_dist_small"], ["_AB_P", "ground_dist_small_P"],
      |["_AC", "ground_dist_large"], ["_AC_P", "ground_dist_large_P"],
      |["_BE", "apparent_height"], ["_BE_P", "apparent_height_P"],
      |["_are_similar", "are_similar"]]
      |tmp.forEach(t => assign.set(t[0],t[1]))
      |aquire = new Map()
      |aquire.set("height","__CD")
      |FrameIT.applySchema("_SimilarTriangles",assign,aquire)""".stripMargin
  val s1 =
    """tip: point = ???
      |foot: point = ??? ground: point = ??? p: point = ??? q: point = ???
      |ground_dist_small = 42 ground_dist_small_P:  |- dist(ground)(q) == ground_dist_small = ???
      |ground_dist_large = 420 ground_dist_large_P:  |- dist(ground)(foot) == ground_dist_large = ???
      |apparent_height = 42 apparent_height_P: |- dist(q)(p) == apparent_height = ???
      |are_similar: |- similar((tip,ground,foot))((p, ground, q)) = ???""".stripMargin

  val assignments = collection.mutable.Map(
    ("_AB_P", "ground_dist_small_P"), ("_AB", "ground_dist_small"),
    ("_A", "ground"), ("_B", "q"), ("_C", "foot"), ("_D", "tip"), ("_E", "p"),
    ("_AC", "ground_dist_large"), ("_AC_P", "ground_dist_large_P"),
    ("_BE", "apparent_height"), ("_BE_P", "apparent_height_P"),
    ("_are_similar", "are_similar"))

  val s2 = //INCORRECT
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