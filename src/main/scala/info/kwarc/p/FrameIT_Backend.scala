package info.kwarc.p

import scala.scalajs.js.annotation._
import scala.scalajs.js

/**
  * A FrameIT SituationTheory (SiTh) is semantically a mutable UPL theory (i.e. a closed [[Module]]),
  * used to store and deduce knowledge about the game-world. In practice, Modules are immutable, so a [[SiTh_handler]]
  * provides the necessary functionality to be used like a mutable [[Module]], while also ensuring nothing contradictory
  * happens when mutating.
  *
  * This trait is more of an API specification, than an abstraction, currently.
  */
trait SiTh_handler {
  def get: Module
  def eval: TheoryValue
  def getErrors: List[SError]
  def tryAdd(decls_String: String): Boolean
  def tryAdd(decls: List[Declaration]): Boolean
  def reset(): Unit
  //def remove(fact_name: String): Either[List[SError], Module]
}

/**
  * A FrameIT Project has a "SituationTheory" (SiTh), a UPL theory (i.e. a closed [[Module]]) which can grow over time.
  * Its current value is accessible via [[SiTh.get]], and new declarations can be added via [[SiTh.tryAdd]]
  */
class FrameITProject private()(implicit debug: Boolean) extends Project(Nil) {
  // SiTh: SituationTheory
  private def SiThFragment(id: Int) = SourceOrigin("SiTh", id.toString)

  private val SiThOrigin = SourceOrigin("SiTh")

  object SiTh extends SiTh_handler {
    private var counter = 0
    private def fragment(i: Int) = s"SiTh$i"
    def currentFragment: String = fragment(counter)

    def get: Module = getEntry(SiThOrigin).checked.lookup("SiTh").asInstanceOf[Module]

    // Helpers to make AST generations more readable
    private def include(name: String) = Include(OpenRef(Path(List(name))))
    private def siThFromContent(decls: List[Declaration]): TheoryValue =
      TheoryValue(List(Module("SiTh", closed = true, decls)))
    private def siThFromContent(decl: Declaration): TheoryValue =
      siThFromContent(List(decl))

    private def updateSiTh(frags: List[Int] = List.range(0,counter+1)) = {
      val includes = for(f <- frags) yield include(fragment(f))
      update(SiThOrigin, siThFromContent(includes))
      val decls = get.decls.filterNot( _.isInstanceOf[Include] )
      update(SiThOrigin, siThFromContent(decls))
      if(debug) println(get)
      checkErrors()
    }

    def tryAdd(decls: List[Declaration]): Boolean = {
      val previousFragment = currentFragment
      counter += 1
      val s = TheoryValue(decls).add(include(previousFragment))
      update(SiThFragment(counter), s)
      updateSiTh()
    }

    def tryAdd(decls_String: String): Boolean = {
      val previousFragment = currentFragment
      counter += 1
      val siThString = s"theory $currentFragment{\ninclude $previousFragment\n$decls_String\n}"
      update(SiThFragment(counter), siThString)
      updateSiTh()
    }

    def reset(): Unit = {
      counter = 0
      entries = entries.filter{ _.source match {
        case SourceOrigin("SiTh", i) if i != null => false
        case _ => true
        }
      }
      updateSiTh()
    }

    def getErrors = getEntry(SiThOrigin).errors.getErrors

    def eval: TheoryValue = {
      val ec = new ErrorCollector
      val ch = new Checker(ec)
      val ip = new Interpreter(Theory.empty)
      var gc = GlobalContext(ip.voc)
      for {
        d <- get.decls
        if d.isInstanceOf[ExprDecl] && d.dfO.isDefined
      } yield {
        val e = d.asInstanceOf[ExprDecl].dfO.get
        var result = ""
        val (eC, eI) = ch.checkAndInferExpression(gc, e)
        gc = gc.append(LocalContext.collectContext(eC))
        val ed = ExprDecl("res", eI, Some(eC), false)
        result = ed.toString
        }
      ??? // checkAndRun(siThEval) doesn't work rn, because it doesn't update the vocab along the way
    }
  }

  def getEntry(so: SourceOrigin): ProjectEntry = get(so)

  def update(so: SourceOrigin, thVal: TheoryValue) = {
    val e = get(so)
    e.parsed = thVal
    e.errors.clear
    e.checkedIsDirty = true
    check(so, false)
  }
}
object FrameITProject{
  def apply(backgroundTheoryContent: String)(implicit debug: Boolean): FrameITProject = {
    val proj = new FrameITProject()
    val btString = s"theory ${proj.SiTh.currentFragment}{\n$backgroundTheoryContent\n}"
    proj.update(SourceOrigin("BackgroundTheory"), btString)
    proj.SiTh.reset()
    proj
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
  private val proj = FrameITProject("x=0")(debug = true)
  var SiTh: SiTh_handler = proj.SiTh

  def main(args: Array[String]): Unit = {
//    JS_addS("x=0")
//    JS_addS("y= x+1 == 1")
//    JS_addS("z= 1+1")
//    JS_addS("a=3")
    //SiTh.eval
    proj.runMaybeRepl(true)
  }

  def CreatesDoubleCheckError() = {
    val parsed = Parser.text(SourceOrigin.anonymous, "x=0", ErrorIgnorer)
    val ch = new Checker(ErrorIgnorer)
    val checked = ch.checkVocabulary(GlobalContext(Nil), parsed, true)(parsed)
    ch.checkVocabulary(GlobalContext(Nil), checked, true)(checked)
    ch.checkVocabulary(GlobalContext(Nil), parsed, true)(parsed)
  }

  // ToDO: Make a useful JS Object
  def makeJSReadable(declaration: Declaration) = declaration.toString

  @JSExport("showSiTh")
  def JS_showSiTh: String = makeJSReadable(SiTh.get)

  @JSExport("SiThErrors")
  def JS_getSiThErrors: String = SiTh.getErrors.mkString("\n")

  /** Add [[Declaration]]s to the SiTh
    *
    * @param decls_String The declarations to add, as raw code string
    * @return True if no error occurred, false otherwise.
    */
  @JSExport("tryAdd")
  def JS_addS(decls_String: String): Boolean = SiTh.tryAdd(decls_String)

  @JSExport("resetSiTh")
  def JS_resetSiTh(): Unit = SiTh.reset()

  def pureValueFact(name: String, fun: ClosedRef, args: List[Expression], value: Float) = {
    val definiendum = Application(fun = fun, args = args)
    val definiens = FloatValue(value)
    VarDecl(
      name,
      ProofType(Equality(positive = true, tp = NumberType.Float, left = definiendum, right = definiens)),
      None,
      mutable = false,
      output = false
    )
  }

}