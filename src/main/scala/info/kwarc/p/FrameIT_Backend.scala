package info.kwarc.p

import scala.collection.SeqMap
import scala.scalajs.js
import js.annotation._
import scala.annotation.tailrec

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
  implicit def gc: GlobalContext = proj.makeGlobalContext()

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

  import js.JSConverters._
  def eval(exprS: String): js.UndefOr[js.Object] = {
    val evalS = s"${proj.Stage.name_curr}{}.$exprS"
    proj.tryEvalTyped(evalS)
      .map{ case (r,t) =>
      new js.Object {
        val result = r.toString
        val `type` = t.toString
      }}
      .toOption
      .orUndefined
  }

  def evalNum(exprS: String): js.UndefOr[Double] = {
    val evalS = s"${proj.Stage.name_curr}{}.$exprS"
    proj.tryEval(evalS)
      .collect { case NumberValue(_, re, _) => re.approx.value }
      .toOption
      .orUndefined
  }

  def evalFuncValueFact(factName: String): js.UndefOr[js.Object] = {
    val exprS = s"${proj.Stage.name_curr}{}.${factName}_P"
    proj.tryEval(exprS)
      .collect { case ValueFact(f, as, v) =>
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
    *
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
    implicit var gc: GlobalContext = proj.makeGlobalContext()
    implicit val useless:Unit = ()
    println(proj.tryEval(s"${proj.Stage.name_curr}{}.height"))
    val tmp1 = proj.tryEval(s"${proj.Stage.name_curr}.height")
    println(Simplify(tmp1.get))
    gc = GlobalContext(proj.SiTh.get)
    val tmp2 = proj.SiTh.lookup("height")//.asInstanceOf[ExprDecl].dfO.get
    println(Simplify(tmp2).dfO)
    val tmp3 = proj.SiTh.lookup("height_P")
    tmp3 match { case ValueFact(n,f, as, v) => println(n,f, as, v) }
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
      tp match {
        case ProofType(Equality(
          true,
          _,
          ap:Application,
          Simplify(NumberValue(_, re, im))
          ))  if im.zero => {
          val (func, args) = uncurried(ap)
          Option(func, args, re.approx.value)
        }
        case _ => None
      }
    }
    @tailrec
    private def uncurried(ap: Application, collectedArgs: List[Expression] = Nil): (Ref, List[Expression]) = {
      val args: List[Expression] = ap.args ++: collectedArgs
      ap.fun match {
        case fun: Ref => (fun,args)
        case app:Application => uncurried(app, args)
        case _ => throw new Exception
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
  def unapply(expr: Expression)(implicit gc: GlobalContext): Option[Expression] = {
    expr match {
      case UndefinedValue(ProofType(formula)) => Option(formula)
      case EVarDecl(_, ProofType(formula), _, _, _) => Option(formula)
      case _ => None
    }
  }
}
