package info.kwarc.p

import info.kwarc.p.FactUtil.{axName, axSuffix}
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
  implicit def gc: GlobalContext = proj.gc
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
      .map(ValueFactHelper.toJS)
      .orUndefined
  def evalFuncValueFact(factName: String): js.UndefOr[js.Object] =
    LoWo
      .lookupValueFact(factName)
      .map(ValueFactHelper.toJS)
      .orUndefined

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
    proj.updateAndCheck(SourceOrigin(""), "theory T1 {i = \"T1.i\", j = i, k:int}\ntheory T2 { i = \"T2.i\", j = i}\nt0=T2{}{.T1.j}\nt1=T2{}.j\nt2=T2.j\nt3=T2{}\nt4=T2{k=1}.j")
    val pe = proj.get(SourceOrigin(""))
    val tmp = for {d <- pe.checked.decls.drop(2)} yield d.dfO.get
    val tmp1 = Parser.text(SourceOrigin(""), "theory T1 {val i : int}, val t1 = T1{val i : int = 1}", ErrorThrower).decls(1).dfO.get
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
      proj applySchema("SimilarTriangles", assignments, SeqMap(("_CD","height"), ("_CD_P","height_P"))),
      LoWo.lookupNum("height"),
      LoWo.lookupValueFact("height"),
      FactUtil.listFacts(proj.findSchema("SimilarTriangles").get).map(f => (f.name, f.factTypeLabel)),
      FactUtil.listFacts(proj.LoWo.asModule).map(f => (f.name, f.factTypeLabel)),
      proj.LoWo.lookupFact[Distance]("height", Distance)
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
      |apparent_height = 0.36
      |apparent_height_P: |- dist(q)(p) == apparent_height = ???
      |ground_dist_small = 0.50
      |ground_dist_small_P:  |- dist(ground)(q) == ground_dist_small = ???;
      |ground_dist_large = 48.25
      |ground_dist_large_P:  |- dist(ground)(foot) == ground_dist_large = ???""".stripMargin

  val assignments = collection.mutable.Map(
    ("_A", "ground"), ("_B", "q"), ("_C", "foot"), ("_D", "tip"), ("_E", "p"),
    ("_AB", "ground_dist_small"),
    ("_AC", "ground_dist_large"),
    ("_BE", "apparent_height"),
    ("_are_similar", "are_similar")
  )
}

/** FrameIT adapted version of [[Substituter]] that renames [[Declaration]]s in a closed [[Module]].
  * Also substitutes [[ClosedRef]] accordingly.
  *
  * TODO This is a bit of a hack. Saver options in the future:
  *  - An advanced version that can traverse deeper, and gathers a valid [[Substitution]] on the way;
  *    Might be useful in general as a "Simplify_mildly"
  *  - More safeguards/sanity-checks, and even less traversal
  */
class RenameRegional(implicit gc: GlobalContext, sub: Substitution) {
  private val subber = new RenameRegional._Substituter(gc)

  def apply(m: Module): Module = {
    if (!m.closed) m
    else m.copyBody(apply(_))
  }

  def apply[S[Declaration] <: scala.collection.SeqOps[Declaration, S, S[Declaration]]](decls: S[Declaration]): S[Declaration] = decls.map(subber(_))

  def apply(decl: Declaration): Declaration = subber(decl)
}

object RenameRegional {
  def apply(sub: Substitution, m: Module)(implicit gc: GlobalContext): Module = {
    if (sub.isIdentity || !m.closed) m
    else m.copyBody(apply(sub, _).toList)
  }
  def apply(sub: Substitution, decls:Seq[Declaration])(implicit gc: GlobalContext): Seq[Declaration] = {
    if (sub.isIdentity) decls
    else {val subber = new _Substituter(gc)
      decls.map(subber(_)(gc,sub))
    }
  }
  def apply(sub: Substitution, decl:Declaration)(implicit gc: GlobalContext): Declaration = {
    if (sub.isIdentity) decl
    else { new _Substituter(gc)(decl)(gc,sub) }
  }

  private class _Substituter(initGC: GlobalContext) extends Substituter(initGC) {
    import SyntaxFragment.matchC

    override def apply(exp: Expression)(implicit gc: GlobalContext, sub: Substitution) = matchC(exp) {
      case ClosedRef(n) if sub.declares(n) && inOriginalRegion => sub(n) match {
        case Some(r: ClosedRef) => r
        case _ => throw IError("unexpected substitute")
      }
      case _ => applyDefault(exp)
    }

    /** Don't traverse into other [[Module]], because [[ClosedRef]] are not valid in there */
    override def apply(d: Declaration)(implicit gc: GlobalContext, sub: Substitution): Declaration = matchC(d){
      case _:Module => d
      case d: ExprDecl if sub.declares(d.name) && inOriginalRegion => sub(d.name) match {
        case Some(ClosedRef(n)) => applyDefault(d.copy(name = n))
        case _ => throw IError("unexpected substitute")
      }
      case _ => applyDefault(d)
    }
  }
}

/*  Experimental factories to make common, but convoluted, declarations easier to interact with.
    There is still redundancy left to eliminate, but it is down to the realm of 'annoying copy-paste",
    not "reinvent the "
 */


/** "Accessors" for [[Declaration]]s of the form ```name: |- func(args) == value```
  * @example {{{
  *           val Distance = new ValueFact(OpenRef(Path("dist")))
  *           ...
  *           expr match{case Distance(args, v) => ...} }}}
  * @todo Allow for `value` to a type other than just [[Double]]
  */
object ValueFactHelper {
  def apply( name: String,
             func: ClosedRef,
             args: List[Expression],
             value: Double
           ): ExprDecl = {
    val tp = ProofType( Equality(
        positive = true,
        tp = NumberType.Float,
        left = Application(func, args),
        right = FloatValue(value)
      )
    )
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

  def tryConvertToDouble(e:Expression): Option[Double] = RealValue.unapply(e).map(_.approx.value)

  def unapply(qty: ExprDecl, defAx: ExprDecl):Option[(String, Ref, List[Expression], Option[Double])] = defAx match {
    case DefiningAxiom(func, args, ClosedRef(qty.name)) if (qty.name+"_P" != defAx.name) => {
      val value = qty.dfO.flatMap(tryConvertToDouble)
      Option(qty.name, func, args, value)
    }
    case _ => None
  }

  def evalFromDefAx(t: {val tp:Type})(implicit gc: GlobalContext): Option[(Ref, List[Expression], Double)] =
    for { (func, args, nv) <- DefiningAxiom.unapply(t)
          value <- tryConvertToDouble(Simplify(gc,nv))
    } yield (func, args, value)

  object DefiningAxiom {
    def unapply(t: {val tp:Type}): Option[(Ref, List[Expression], Expression)] = t.tp.skipUnknown match {
      case ProofType(Equality(true, _, Curried(func, args), expr)) => Option(func,args,expr)
      case ProofType(Equality(true, _, expr, Curried(func, args))) => Option(func,args,expr)
      case _ => None
    }
  }
}

object Curried {
  def unapply(ap: Application): Option[(Ref, List[Expression])] = uncurried(ap)
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

/** "Accessors" for [[Declaration]]s of the form ```name: |- prop (args)``` */
object AssertionFactHelper {
  def apply( name: String, formula: Expression ): ExprDecl = {
    val tp = ProofType(formula)
    val modifiers = Modifiers(closed = false, mutable = false)
    ExprDecl(name, LocalContext.empty, tp, dfO = None, None, modifiers)
  }

  /** @param decl Has to be an [[ExprDecl]]; allows for arbitrary [[Declaration]]s, because
    *             the type is often hard to narrow beforehand
    */
  def unapply(decl: Declaration): Option[(String, Ref, List[Expression])] = {
    decl match {
      case ExprDecl(name,_,ProofType(Curried(prop,args)),_,_,_) => Option(name, prop, args)
      case _ => None
    }
  }
}

trait Fact{
  val name: String
  val factTypeLabel: String
  def toDeclsString: String
}
trait FactClass[+F<:Fact] {
  /** Try to interpret [[ExprDecl]]s as a [[Fact]] */
  val fromDecls: PartialFunction[(ExprDecl, Option[ExprDecl]), F] //= (fromDeclsO _).tupled.unlift

  /** Those would require generalization over the parameters of the companion class */
  //  def unapply(fact:F): Option[???]
  //  def apply(???): F
  //  def unapply(decls:(ExprDecl,Option[ExprDecl])): Option[???] = fromDecls.unapply(decls).flatMap(unapply)

  protected val BGRef: PartialFunction[OpenRef, String] = {case OpenRef(Path(List(name))) => name}
}

abstract class FuncValueFact[F<:Fact](val funcName:String) extends FactClass[F] {
  def unapply(fact:F): Option[(String, List[Expression], Option[Double])]
  def apply(name:String, args:List[Expression], value:Option[Double]): F

  def unapply(decls:(ExprDecl,Option[ExprDecl])): Option[(String, List[Expression], Option[Double])] =
    fromDecls.unapply(decls).flatMap(unapply)

  val fromDecls: PartialFunction[(ExprDecl, Option[ExprDecl]), F] = {
    case (qty:ExprDecl,
          Some(defAx@ValueFactHelper.DefiningAxiom(BGRef(`funcName`), args, ClosedRef(refName))))
      if FactUtil.areDeclAndAx(qty, defAx) && refName == defAx.name.stripSuffix(axSuffix) => {
      val value = qty.dfO.flatMap(ValueFactHelper.tryConvertToDouble)
      apply(qty.name, args, value)
    }
  }

  def makeDeclsString(name:String, argsString:List[String], value:Option[Double]): String = {
    var declCode: String =  s"$name"
    value.foreach(d => declCode += s" = $d")
    val axCode = s"${axName(name)}: |- $funcName ${argsString.mkString(" ")}"
    declCode + "\n" + axCode
  }
}

case class Distance(name:String, args:List[Expression], value:Option[Double]) extends Fact {
  val factTypeLabel = "distance"

  def toDeclsString: String = Distance.makeDeclsString(name, args.map(_.toString), value)
}
object Distance extends FuncValueFact[Distance]("dist") with FactClass[Distance]


case class Point(name:String) extends Fact {
  val factTypeLabel: String = "point"
  def toDeclsString: String = s"$name: point"
}
object Point extends FactClass[Point]{
  val fromDecls: PartialFunction[(ExprDecl, Option[ExprDecl]), Point] = {
    case (ExprDecl(name,_, BGRef("point"),_,_,_), None) => Point(name)
  }

  def unapply(decl: ExprDecl): Option[String] = fromDecls.lift((decl,None)).flatMap(unapply)
}


abstract class AssertionFact [F<:Fact](val propName:String) extends FactClass[F] {
  def unapply(fact:F): Option[(String, List[Expression])]
  def apply(name:String, args:List[Expression]): F

  def unapply(decls:(ExprDecl,Option[ExprDecl])): Option[(String, List[Expression])] =
    fromDecls.lift(decls).flatMap(unapply)

  val fromDecls: PartialFunction[(ExprDecl, Option[ExprDecl]), F] = {
    case (AssertionFactHelper(name,BGRef(`propName`), args), None) => apply(name, args)
  }

  def makeDeclsString(name:String, argsString:List[String]): String =
    s"$name: |- $propName ${argsString.mkString(" ")}"
}

case class Similar(name: String, args: List[Expression]) extends Fact {
  val factTypeLabel: String = "similar"

  def toDeclsString: String = Similar.makeDeclsString(name, args.map(_.toString))
}
object Similar extends AssertionFact[Similar]("similar") with FactClass[Similar]

object FactUtil {
  import Util.LookupDecl
  final val axSuffix = "_P"
  val knownFactClasses:List[FactClass[Fact]] = List(Distance, Point, Similar)

  @inline
  def axName(name:String): String = name + axSuffix
  @inline
  def isAxName(name:String): Boolean = name.endsWith(axSuffix)
  /** [[axDecl]] is the defining axiom of [[decl]] */
  def areDeclAndAx(decl: ExprDecl, axDecl: ExprDecl): Boolean = axDecl.name == axName(decl.name)

  val tryAll: List[FactClass[Fact]] => (ExprDecl, Option[ExprDecl]) => Option[Fact] = fcs => {
    //val orElseApply = (pf:PartialFunction[(ExprDecl, Option[ExprDecl]), Fact], fc:FactClass[Fact]) => pf.orElse((fc.apply _).tupled.unlift)
    fcs.map(_.fromDecls).fold(PartialFunction.empty[(ExprDecl, Option[ExprDecl]), Fact])(_.orElse(_)).lift(_,_)
  }
  /** Check all [[knownFactClasses]] whether their [[FactClass.fromDecls]] can be applied to this tuple*/
  def tryAllKnownFactFlasses(decl: ExprDecl, defAxO: Option[ExprDecl]) = {
    tryAll(knownFactClasses)(decl,defAxO)
  }

  def listFacts(m:Module): List[Fact] = {
    for {
      d <- m.decls
      name <- d.nameO
      if !isAxName(name)
      decl <- m.lookupDecl[ExprDecl](name)
      defAxO = m.lookupDecl[ExprDecl](axName(name))
      fact <- tryAllKnownFactFlasses(decl, defAxO)
    } yield fact
  }
}
