package info.kwarc.p

import scala.scalajs.js.annotation._
import scala.scalajs.js
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
  def tryAdd(decls_String: String): Boolean
  def tryAdd(decls: List[Declaration]): Boolean
  def reset(): Unit
  def SiThDecls: List[Declaration]
  //def remove(fact_name: String): Either[List[SError], Module]
  //def eval: TheoryValue
}

/**
  * A FrameIT Project has a "SituationTheory" (SiTh), a UPL theory (i.e. a closed [[Module]]) which can grow over time.
  * This is implemented via a special [[ProjectEntry]]
  * Its current value is accessible via [[getSiTh]], and new declarations can be added via [[tryAdd]]
  */
class FrameITProject private(main: Option[Expression] = None)(implicit debug: Boolean)
  extends Project(Nil, main) with SiTh_handler {
  import info.kwarc.p.FrameITProject._

  private var counter = 0
  def currentFragment: String = fragment(counter)
  object SiTh extends ProjectEntry(SiThOrigin) {
    /** Set the SiTh to the combination of all [[Declaration]]s of all SiThFragments
      *
      * @return `false` iff the resulting [[ProjectEntry]] does not type-check
      */
    def update() = updateAsCombination(List.range(0, counter + 1))

    def updateAsCombination(frags: List[Int]) = {
      val includes = for (f <- frags) yield include(fragment(f))
      set(includes)

      removeIncludes()
      if (debug) println(toString)
      !hasErrors
    }
    def set(fromDecls: List[Declaration]): TheoryValue = {
      updateAndCheck(SiThOrigin, TheoryValue(Module("SiTh", closed = true, fromDecls)))
    }
    def removeIncludes(): TheoryValue =
      set(decls.filterNot(_.isInstanceOf[Include]))
    def asModule: Module =
      getVocabulary
        .decls
        .collectFirst{
          case m: Module if m.name == "SiTh" => m
        }
        .getOrElse(Module("SiTh", closed = true, Theory.empty))
    def decls: List[Declaration] = asModule.decls
    override def toString: String =
      source.toString ++ " ::\n" ++ decls.mkString("{", "\n ", "\n}").indent(2)
  }

  def SiThDecls = SiTh.decls
  def getSiTh = SiTh.asModule
  def tryAdd(decls_String: String): Boolean = {
    val previousFragment = currentFragment
    counter += 1
    val siThString = s"theory $currentFragment{\ninclude $previousFragment\n$decls_String\n}"
    updateAndCheck(SiThFragment(counter), siThString)
    SiTh.update()
  }
  @inline
  final def tryAdd(decls: List[Declaration]): Boolean = tryAdd(decls.mkString("\n"))
  def reset(): Unit = {
    counter = 0
    entries = entries.filter {
      _.source match {
      case SourceOrigin("SiTh", i) if i != null => false
      case _ => true
      }
    }
    SiTh.update()
  }
  def getSiThErrors: List[SError] = SiTh.errors.getErrors
  def updateAndCheck(so: SourceOrigin, thVal: TheoryValue): TheoryValue = {
    val e = get(so)
    e.errors.clear
    e.parsed = thVal
    e.checkedIsDirty = true
    check(so, false)
  }
  /** Find the corresponding [[ProjectEntry]] in [[entries]].
    *
    * If there isn't one yet, create it, and insert it as the __second to last__ entry, before the [[SiTh]]
    */
  override def get(so: SourceOrigin): ProjectEntry = entries.find(_.source == so).getOrElse {
    val e = new ProjectEntry(so)
    entries = entries match {
      case es :+ sith => es :+ e :+ sith
      case _ => e :: Nil
    }
    e
  }
  def tryReadAndRun(input: String): Try[Expression] = {
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
  private def SiThFragment(id: Int) = SourceOrigin("SiTh", id.toString)
  private val SiThOrigin: SourceOrigin = SourceOrigin("SiTh")
  def apply(backgroundTheoryContent: String, main: String = "")(implicit debug: Boolean): FrameITProject = {
    val so = SourceOrigin("BackgroundTheory")
    val mainE = Try(Parser.expression(SiThOrigin, main, ErrorThrower)).toOption
    val proj = new FrameITProject(mainE)
    proj.entries = List(proj.SiTh)

    // Add the BackgroundTheory. Compare [[proj.tryAdd]]
    val btString = s"theory ${proj.currentFragment}{\n$backgroundTheoryContent\n}"
    proj.updateAndCheck(so, btString)
    proj.SiTh.update()
    proj
  }
  private def fragment(i: Int) = s"SiTh$i"
  // Helpers to make AST generations more readable
  private def include(name: String) = Include(OpenRef(Path(List(name))))
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
    JS_addS("x:in")
    JS_addS("a = x+2")
    println(JS_eval("SiTh{x=1}.a"))
    //proj.runMaybeRepl(true)
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
  def JS_addS(decls_String: String): Boolean = proj.tryAdd(decls_String)

  def resetLevel(): Unit = proj.reset()

  @JSExport("newLevel")
  def JS_newProject(backgroundTheoryContent: String): Unit = { proj = FrameITProject(backgroundTheoryContent) }

  @JSExport("eval")
  def JS_eval(exprS: String): String = {
    val ts = proj.tryReadAndRun(exprS)
    ts.fold(err => err.toString, expression => expression.toString)
  }

}

/** Experimental factory to make common, but convoluted, declarations easier to interact with.*/
object ValueFact {
  ////// Useful conversions.
  import scala.language.implicitConversions
  implicit def varDeclAsDecl(expr: VarDecl): ExprDecl = expr match {
    case VarDecl(name, tp, dfO, mutable, output) => ExprDecl(name, tp, dfO, None, Modifiers(false, mutable))
  }
  implicit def exprDeclAsExpr(decl: ExprDecl): VarDecl = decl match {
    case ed: ExprDecl => VarDecl(ed.name, ed.tp, ed.dfO, ed.modifiers.mutable)
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
    ExprDecl(name, tp, dfO = None, None, modifiers)
  }

  def unapply(decl: ExprDecl): Option[(ClosedRef, List[Expression], Double)] = {
    decl.tp match {
      case ProofType(Equality(true, NumberType.Float, Application(fun: ClosedRef, args), FloatValue(value))) =>
        Some(fun, args, value)
      case _ => None
    }
  }
}