package info.kwarc.p

import info.kwarc.p.File.read

import scala.collection.{SeqMap, mutable}
import scala.scalajs.js
import js.annotation._
import scala.annotation.tailrec
import js.JSConverters._

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
  implicit var proj: FrameITProject = FrameITProject("","")
  implicit def gc: GlobalContext = LoWo.gc
  def LoWo = proj.LoWo
  //def LoWo = proj.LoWo.asModule

  /** ToDO: Make a useful JS Object */
  def makeJSReadable(declaration: Declaration) = declaration.toString

  def getLoWoErrors: String = LoWo.errors.toString
  def getAllErrors = proj.getErrors.mkString("\n")

  /** Add a single declaration fact to the LoWo
    *
    * @param decls_String The raw code string of the fact declaration
    * @return `true` if no error occurred, `false` otherwise.
    */
  def add(decls_String: String): Boolean = LoWo.add(decls_String)

  /** Add a multi declaration fact to the LoWo
    *
    * @param decls_Strings The raw code strings of the fact's declarations
    * @return `true` if no error occurred, `false` otherwise.
    * @note We use [[mutable.Seq]], because it is implicitly convertable from JS.Array.
    *       decls_Strings is not mutated.
    */
  def add(decls_Strings: mutable.Seq[String]): Boolean = LoWo.add(decls_Strings.toSeq)

  /** @see [[proj.LoWo.add]] */
  def add(decls_Strings: Seq[String]): Boolean = LoWo.add(decls_Strings)

  def resetLevel(): Unit = LoWo.reset()

  def newLevel(backgroundTheoryContent: String, schemataContent: String): Boolean = {
    proj = FrameITProject(backgroundTheoryContent, schemataContent)
    !proj.hasErrors
  }


  def eval(exprS: String): js.UndefOr[js.Object] = {
    LoWo.evalTyped(exprS)
      .map{ case (r,t) =>
        new js.Object {
          val result = r.toString
          val `type` = t.toString
        }
      }
      .orUndefined
  }
  def lookup(name:String): js.UndefOr[js.Object] = LoWo.lookup(name).orUndefined

  def lookupNum(name:String): js.UndefOr[Double] = LoWo.lookupNum(name).orUndefined
  def evalNum(exprS: String): js.UndefOr[Double] = {
    LoWo
      .eval(exprS)
      .collect { case RealValue(re) => re.approx.value }
      .orUndefined
  }

  def lookupValueFact(factName: String): js.UndefOr[js.Object] =
    LoWo
      .lookupValueFact(factName)
      .map(ValueFact.toJS)
      .orUndefined
  def evalFuncValueFact(factName: String): js.UndefOr[js.Object] = {
    LoWo
      .eval(factName)
      .collect { case ValueFact(vf) => ValueFact.toJS(vf) }
      .orUndefined
  }

  /** @see [[FrameITProject.applySchema]]
    *
    */
  def applySchema(
      schema: String,
      assignReq: js.Map[String, String],
      assignRes: js.Map[String, String]
  ) = {
    proj.applySchema(schema, assignReq, assignRes)
  }

  def debugPrintVerbose(): Unit = println(proj.toStringVerbose)
}

object BackendTests {
  import FrameIT_Backend._
  def main(args: Array[String]): Unit = {
    gameplayTest()
  }

  /** private, so scala.js doesn't need to see [[File]] */
  private def gameplayTest() = {
    //proj = FrameITProject(File("test/FrameIt/Gameplay_Example/gameplay.pp"))
    val bg = read(File("test/FrameIt/Gameplay_Example/background.p"))
    val schema = read(File("test/FrameIt/Gameplay_Example/schema.p"))
    proj = FrameITProject(bg,schema)
    LoWo.reset()
    val tests = List(
      s1.split(";").map(_.linesIterator.toSeq).map(add).mkString(" "),
      proj applySchema("SimilarTriangles", assignments, SeqMap(("_CD","height"),("_CD_P","height_P"))),
      LoWo.lookupNum("height"),
      LoWo.lookupValueFact("height"),
    )
    tests.foreach(println)
    val stopHereForDebug: Unit= ()
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
      |  _CD = _AC * _BE / _AB  _CD_P: |- dist(_C)(_D) == __CD = ???
      |}""".stripMargin
  val jsSchemaApp =
    """assign = new Map()
      |tmp = [["_A", "ground"], ["_B", "q"], ["_C", "foot"], ["_D", "tip"], ["_E", "p"],
      |["_AB", "ground_dist_small"], ["_AB_P", "ground_dist_small_P"],
      |["_AC", "ground_dist_large"], ["_AC_P", "ground_dist_large_P"],
      |["_BE", "apparent_height"], ["_BE_P", "apparent_height_P"],
      |["_are_similar", "are_similar"]]
      |tmp.forEach(t => assign.set(t[0],t[1]))
      |acquire = new Map()
      |acquire.set("height","__CD")
      |FrameIT.applySchema("_SimilarTriangles",assign,acquire)""".stripMargin
  val s1 =
    """tip: point; foot: point; ground: point; p: point
      |q: point
      |are_similar: |- similar((ground, foot, tip))((ground, q, p)) = ???
      |apparent_height = 36
      |apparent_height_P: |- dist(q)(p) == apparent_height = ???
      |ground_dist_small = 50
      |ground_dist_small_P:  |- dist(ground)(q) == ground_dist_small = ???;
      |ground_dist_large = 48.25
      |ground_dist_large_P:  |- dist(ground)(foot) == ground_dist_large = ???""".stripMargin

  val assignments = collection.mutable.Map(
    ("_A", "ground"), ("_B", "q"), ("_C", "foot"), ("_D", "tip"), ("_E", "p"),
    ("_AB", "ground_dist_small"), ("_AB_P", "ground_dist_small_P"),
    ("_AC", "ground_dist_large"), ("_AC_P", "ground_dist_large_P"),
    ("_BE", "apparent_height"), ("_BE_P", "apparent_height_P"),
    ("_are_similar", "are_similar")
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
  def apply(gc: GlobalContext, sub: Substitution, m: Module): Module = {
    if (sub.isIdentity || !m.closed) m
    else {val subber = new _Substituter(gc)
      m.copyBody(_.map(subber(_)(gc,sub)))
    }
  }
  def apply(gc: GlobalContext, sub: Substitution, decls:Seq[Declaration]): Seq[Declaration] = {
    if (sub.isIdentity) decls
    else {val subber = new _Substituter(gc)
      decls.map(subber(_)(gc,sub))
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

// Experimental factories to make common, but convoluted, declarations easier to interact with.

/** "Accessors" for [[Declaration]]s of the form ```name: |- func(args) == value```
  *
  * @todo ValueFacts actually consist of two declarations. But that's probably a lot uglier to tackle
  * @todo Allow for `value` to a type other than just [[Double]]
  */
object ValueFact {
  def apply( name: String,
             func: ClosedRef,
             args: List[Expression],
             value: Double
           ): ExprDecl = {
    val tp = ValueFactType(func, args, value)
    val modifiers = Modifiers(closed = false, mutable = false)
    //VarDecl(name, tp, dfO = None, mutable = false)
    ExprDecl(name, LocalContext.empty, tp, dfO = None, None, modifiers)
  }

  def toJSP(f: Ref, as: List[Expression], v:Double): js.Object = {
    new js.Object {
      val func = f.toString
      val args = as.map(_.toString).toJSArray
      val value = v
    }
  }

  def toJS: ((Ref, List[Expression], Double)) => js.Object = (toJSP _).tupled

  /*
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
  */

  /** @param decl Has to be an [[ExprDecl]]; allows for arbitrary [[Declaration]]s, because
    *             the type is often hard to narrow beforehand
    */
  def unapply(decl: Declaration)(implicit gc: GlobalContext): Option[(String, Ref, List[Expression], Double)] = {
    decl match {
      case ExprDecl(name,_,ValueFactType(func,args,res),_,_,_) => Option(name, func, args, res)
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
  /** Helper for readability and easier adaption.
    *
    * Basically just a recursive application of the same pattern
    */
  private object ValueFactType {
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
      tp.skipUnknown match {
        case ProofType(Equality(true,_,ap:Application,nv)) =>
          (Simplify(gc,nv), uncurried(ap)) match {
            case (RealValue(re),Some((func, args))) =>
              Option(func, args, re.approx.value)
            case _ => None
         }
        case _ => None
      }
    }
    @tailrec
    private def uncurried(ap: Application, collectedArgs: List[Expression] = Nil): Option[(Ref, List[Expression])] = {
      val args: List[Expression] = ap.args ++: collectedArgs
      ap.fun match {
        case fun: Ref => Option(fun,args)
        case app:Application => uncurried(app, args)
        case _ => None
      }
    }
  }
}

/** "Accessors" for [[Declaration]]s of the form ```name: |- formula``` */
object AssertionFact {
  def apply( name: String, formula: Expression ): ExprDecl = {
    val tp = ProofType(formula)
    val modifiers = Modifiers(closed = false, mutable = false)
    ExprDecl(name, LocalContext.empty, tp, dfO = None, None, modifiers)
  }

  /** @param decl Has to be an [[ExprDecl]]; allows for arbitrary [[Declaration]]s, because
    *             the type is often hard to narrow beforehand
    */
  def unapply(decl: Declaration)(implicit gc: GlobalContext): Option[(String, Expression)] = {
    decl match {
      case ExprDecl(name,_,ProofType(formula),_,_,_) => Option(name, formula)
      case _ => None
    }
  }

  /**  */
  val fromExpression: Expression => Option[Expression] = {
      case UndefinedValue(ProofType(formula)) => Option(formula)
      case EVarDecl(_, ProofType(formula), _, _, _) => Option(formula)
      case _ => None
  }
}
