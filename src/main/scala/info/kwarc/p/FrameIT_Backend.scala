package info.kwarc.p

import scala.collection.SeqMap
import scala.scalajs.js
import scala.scalajs.js.UndefOr
import scala.scalajs.js.annotation._

/** The API for interfacing with the Backend from the outside.
  * Hides all the fancy Scala and UPL stuff [[FrameITProject]] can use, and instead provides simple return types.
  *
  * (Currently, the only expected "outside" is JS)
  */
@JSExportTopLevel("FrameIT")
@JSExportAll
object FrameIT_Backend {
  import Gameplay._
  implicit val debug: Boolean = false
  var proj = FrameITProject("", "")

  def main(args: Array[String]): Unit = {
    val path = File("Test/temp.pp").canonical
    val proj = Project.fromFile(path, None)
    val voc = proj.check(true)
    val gc = GlobalContext(voc)
    val tS = Solver.solve(gc, OpenRef(Path("slingshot_example", "Slingshot_test")))
    println(tS)
    //gameplayTest()
  }

  /** private, so scala.js doesn't need to see [[File]] */
  private def gameplayTest() = {
    //proj = FrameITProject(File("test/FrameIt/Gameplay_Example/gameplay.pp"))
    newLevel(bg, schema)

//    val pointsR = List(("_A", "ground"), ("_B", "q"), ("_C", "foot"), ("_D", "tip"), ("_E", "p"))
//    val distsR = List(("_AB", "ground_dist_small"), ("_AC", "ground_dist_large"),
//      ("_BE", "apparent_height"))
//    pointsR.foreach {case (_, n) => add(s"$n: point = ???")}
//    add(s"${distsR(0)._2}: float = 42")
//    add(s"${distsR(1)._2}: float = 420")
//    add(s"${distsR(2)._2}: float = 21")
    add(s1)
    proj applySchema ("_SimilarTriangles", assignments, SeqMap(
      ("__CD", "height"),
      ("__CD_P", "height_P")
    ))
    if (!proj.checkErrors()) println(proj.tryEval("SiTh{}.height"))
    implicit val gc = proj.SiTh.context
    proj.tryEval("SiTh{}.height_P").collect{ case (ValueFact(f, as, v),_) => println(f, as, v) }
    //val tmp = evalFuncValueFact("SiTh{}.height_P")
    println(showSiTh)
  }

  // ToDO: Make a useful JS Object
  // def makeJSReadable(declaration: Declaration) = declaration.toString

  def showSiTh: String = proj.SiTh.toString

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

  def newLevel(
      backgroundTheoryContent: String,
      schemataContent: String
  ): Boolean = {
    proj = FrameITProject(backgroundTheoryContent, schemataContent)
    !proj.hasErrors
  }

  import js.JSConverters._
  def eval(exprS: String): UndefOr[js.Object] = {
    proj.tryEval(exprS)
      .map{ case (r,t) =>
      new js.Object {
        val result = r.toString
        val `type` = t.toString
      }}
      .toOption
      .orUndefined
  }

  def evalNum(exprS: String): js.UndefOr[Double] = {
    proj.tryEval(exprS)
      .collect { case (NumberValue(_, re, _),_) => re.approx.value }
      .toOption
      .orUndefined
  }

  def evalFuncValueFact(factName: String): UndefOr[js.Object] = {
    val exprS = s"SiTh{}.${factName}_P"
    implicit val gc = GlobalContext(proj.SiTh.get)
    proj.tryEval(exprS)
      .collect { case (ValueFact(f, as, v),_) =>
        new js.Object {
          val func = f.toString
          val args = as.map(_.toString).toJSArray
          val value = v
        }
      }
      .toOption
      .orUndefined
  }

  /** @see [[FrameITProject.applySchema]]
    */
  def applySchema(
      schema: String,
      assignReq: js.Map[String, String],
      assignRes: js.Map[String, String]
  ) = {
    proj.applySchema(schema, assignReq, assignRes)
  }

  def debugPrintVerbose() = proj.debugPrintVerbose()
}

object Gameplay {

  /** The Background
    */
  val bg =
    """type point
      |type triangle = (point,point,point)
      |dist: (point, point) -> float
      |similar: triangle -> triangle -> bool
      |""".stripMargin

  /** The used Schema */
  val schema =
    """theory InterceptTheorem{
      |  _A: point   _B: point  _C: point  _D: point  _E: point
      |  _AB: float  _AB_P: |- dist(_A, _B) == _AB
      |  _AC: float  _AC_P: |- dist(_A, _C) == _AC
      |  _BE: float  _BE_P: |- dist(_B, _E) == _BE
      |  //_are_similar: |- similar((_D,_A,_C))((_E,_A,_B))
      |  __CD = _AC * _BE / _AB  __CD_P: |- dist(_C, _D) == __CD = ???
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
      |ground_dist_small = 42 ground_dist_small_P:  |- dist(ground, q) == ground_dist_small = ???
      |ground_dist_large = 420 ground_dist_large_P:  |- dist(ground, foot) == ground_dist_large = ???
      |apparent_height = 42 apparent_height_P: |- dist(q, p) == apparent_height = ???
      |are_similar: |- similar((tip,ground,foot))((p, ground, q)) = ???""".stripMargin

  val assignments = collection.mutable.Map(
    ("_AB_P", "ground_dist_small_P"),
    ("_AB", "ground_dist_small"),
    ("_A", "ground"),
    ("_B", "q"),
    ("_C", "foot"),
    ("_D", "tip"),
    ("_E", "p"),
    ("_AC", "ground_dist_large"),
    ("_AC_P", "ground_dist_large_P"),
    ("_BE", "apparent_height"),
    ("_BE_P", "apparent_height_P")
  )

  val s2 = //INCORRECT
    """realize _SimilarTriangles
      |_A = tip _B = p _C = ground _D = q _E = foot
      |_CD = ground_dist_small _CD_P = ground_dist_small_P
      |_CE = ground_dist_large _CE_P = ground_dist_large_P
      |_DB = apparent_height _DB_P = apparent_height_P
      |_are_similar = are_similar""".stripMargin
}

/** Experimental factory to make common, but convoluted, declarations easier to interact with. */
object ValueFact {
  object ValueFactType {
    def apply(func: Ref, args: List[Expression], value: Double): ProofType = {
      ProofType(
        Equality(
          positive = true,
          tp = NumberType.Float,
          left = Application(func, args),
          right = FloatValue(value)
        )
      )
    }

    def unapply(tp: Type)(implicit gc: GlobalContext): Option[(Ref, List[Expression], Double)] = {
      tp match {
        case ProofType(Equality(
          true,
          NumberType.Float,
          Application(fun: Ref, args),
          v
        )) => Simplify(v)(gc, ()) match {
          case NumberValue(_, r, z) if z.zero => Some(fun, args, r.approx.value)
          case _ => None
        }
        case _ => None
      }
    }
  }


  def apply(
      name: String,
      func: ClosedRef,
      args: List[Expression],
      value: Double
  ) = {
    val tp = ValueFactType(func, args, value)
    val modifiers = Modifiers(closed = false, mutable = false)
    //VarDecl(name, tp, dfO = None, mutable = false)
    ExprDecl(name, LocalContext.empty, tp, dfO = None, None, modifiers)
  }

  def apply2(
             name: String,
             func: ClosedRef,
             args: List[Expression],
             value: Double
           ) = {
    val tp = ValueFactType(func, args, value)
    val modifiers = Modifiers(closed = false, mutable = false)
    //VarDecl(name, tp, dfO = None, mutable = false)
    EVarDecl(name, tp, dfO = None, mutable = false, output = false)
  }

  /** @param decl Has to be a [[SymbolDeclaration]]; allows for arbitrary [[Declaration]]s, because
    *             the type is often hard to narrow beforehand
    */
  def unapply(decl: Declaration)(implicit gc: GlobalContext): Option[(String, Ref, List[Expression], Double)] = {
    decl match {
      case d: SymbolDeclaration =>
        for((f,as,v) <- ValueFactType.unapply(d.tp))
        yield (d.name, f, as, v)
      case _ => None
    }

  }

  def unapply(expr: Expression)(implicit gc: GlobalContext): Option[(Ref, List[Expression], Double)] = {
    expr match {
      case UndefinedValue(ValueFactType(f,as,v)) => Option(f,as,v)
      case EVarDecl(_, ValueFactType(f,as,v), _, _, _) => Option(f,as,v)
      case _ => None
    }
  }
}
