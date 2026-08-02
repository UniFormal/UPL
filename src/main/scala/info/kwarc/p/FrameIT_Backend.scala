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
  implicit val debug: Boolean = false
  var proj = FrameITProject("","")

  /** ToDO: Make a useful JS Object */
  def makeJSReadable(declaration: Declaration) = declaration.toString

  def showSiTh: String = proj.SiTh.toString

  def getSiThErrors: String = proj.SiTh.errors.toString
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
    val evalS = s"${proj.Stage.name_curr}{}.$exprS"
    val triedExpression = proj.tryEval(evalS)
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

object BackendTests {
  import FrameIT_Backend._
  def main(args: Array[String]): Unit = {
    gameplayTest()
//    proj = FrameITProject(File(args(0)))
//    val gc = proj.makeGlobalContext()
//    val tS = Solver.solve(gc, OpenRef(Path("Slingshot", "Slingshot_test")))
//    Solver.printAsTheory("Result", tS.decls)
//    add(tS.decls.mkString("\n"))
//    proj.checkErrors()
//    add("i:int=0")
//    println(showSiTh)
  }

  /** private, so scala.js doesn't need to see [[File]] */
  private def gameplayTest() = {
    proj = FrameITProject(File("test/FrameIt/Gameplay_Example/gameplay.pp"))
    //newLevel(bg,schema)
    //add(s1)
    proj applySchema("SimilarTriangles", assignments, SeqMap(("CD","height"),("CD_P","height_P"))) // ("height_P","__CD_P") doesn't work right now
    println(proj.tryEval(s"${proj.Stage.name_curr}{}.height"))
    val tmp1 = proj.tryEval(s"${proj.Stage.name_curr}.height")
    println(Simplify(proj.makeGlobalContext(),tmp1.get))
    val tmp2 = proj.SiTh.lookup("height")//.asInstanceOf[ExprDecl].dfO.get
    println(Simplify(GlobalContext(proj.SiTh.get),tmp2).dfO)
    val stopHereForDebug: Unit= ()
    //debugPrintVerbose()
  }
  /** The Background */
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
      |ground_dist_small = 42
      |ground_dist_small_P:  |- dist(ground)(q) == ground_dist_small = ???
      |ground_dist_large = 420
      |ground_dist_large_P:  |- dist(ground)(foot) == ground_dist_large = ???
      |apparent_height = 42
      |apparent_height_P: |- dist(q)(p) == apparent_height = ???
      |are_similar: |- similar((tip,ground,foot))((p, ground, q)) = ???""".stripMargin

  val assignments = collection.mutable.Map(
    ("AB_P", "ground_dist_small_P"), ("AB", "ground_dist_small"),
    ("A", "ground"), ("B", "q"), ("C", "foot"), ("D", "tip"), ("E", "p"),
    ("AC", "ground_dist_large"), ("AC_P", "ground_dist_large_P"),
    ("BE", "apparent_height"), ("BE_P", "apparent_height_P"),
    //("are_similar", "are_similar")
  )
}

/** FrameIT adapted version of [[Substituter]] that substitutes [[ClosedRef]] in a closed [[Module]]
  *
  * TODO This is a bit of a hack. Saver options in the future:
  *  - An advanced version that can traverse deeper, and gathers a valid [[Substitution]] on the way;
  *    Might be useful in general as a "Simplify_mildly"
  *  - More safeguards/sanity-checks, and even less traversal
  */
object Regional_Substituter {
  def apply(gc: GlobalContext, sub: Substitution, m: Module) = {
    if (sub.isIdentity || !m.closed) m
    else {val subber = new _Substituter(gc)
      m.copyF(_.map(subber(_)(gc,sub)))
    }
  }

  private class _Substituter(initGC: GlobalContext) extends Substituter(initGC) {
    import SyntaxFragment.matchC

    override def apply(exp: Expression)(implicit gc: GlobalContext, sub: Substitution) = matchC(exp) {
      case ClosedRef(n) if n != "" && inOriginalRegion => sub.lookupO(n) match {
        case Some(EVarDecl(_, _, Some(df), _, _)) => df
        case Some(_) => throw IError("unexpected substitute")
        case None => exp
      }
      case _ => applyDefault(exp)
    }

    /** Don't traverse into other [[Module]], because [[ClosedRef]] are not valid in there */
    override def apply(d: Declaration)(implicit gc: GlobalContext, sub: Substitution): Declaration = matchC(d){
      case _:Module => d
      case _ => applyDefault(d)
    }
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
