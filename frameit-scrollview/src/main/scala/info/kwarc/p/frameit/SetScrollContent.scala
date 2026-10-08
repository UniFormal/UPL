package info.kwarc.p.frameit

import org.scalajs.dom
import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel
import scala.scalajs.js.JSConverters._
import scala.scalajs.concurrent.JSExecutionContext.Implicits.queue
import scala.concurrent.Future
import scala.util.control.NonFatal


object SetScrollContent {

  var lastScrollUri: String = ""
  var currentScroll: Option[Scroll] = None


  @JSExportTopLevel("RenderScroll")
  def renderScroll(json: js.UndefOr[String] = js.undefined): Unit = {
    val source = json.toOption.orElse(
      Option(dom.document.querySelector("#Unity-Data-Interface"))
        .flatMap(el => Option(el.getAttribute("data-scroll-dynamic")))
        .map(htmlDecode)
    )
    source match {
      case None => dom.console.error("No Scroll found (neither passed nor in the Unity-Data-Interface)")
      case Some(text) =>
        val parsed =
          try Some(ApiParser.backendObjectFromJson(js.JSON.parse(text)))
          catch { case NonFatal(e) => dom.console.error(e.getMessage); None }
        parsed match {
          case Some(scroll: Scroll) =>
            currentScroll = Some(scroll)
            scroll.render()
          case _ =>
            dom.console.error("Cannot parse this as scroll:\n", text)
        }
    }
  }

  private def notifyUnity(f: Fact): Unit =
    if (js.typeOf(js.Dynamic.global.returnSchemaApplicationResult) == "function") {
      val json = f match {
        case s: LineSegmentFact =>
          def unityId(uplName: String) = FactRegistry.byUplName(uplName).fold(uplName)(_.uri)
          js.JSON.stringify(js.Dynamic.literal(
            id = s.uri, pid1 = unityId(s.p1), pid2 = unityId(s.p2),
            distance = s.length.orUndefined, label = s.UPL_name))
        case other =>
          js.JSON.stringify(js.Dynamic.literal(id = other.uri, label = other.UPL_name))
      }
      js.Dynamic.global.returnSchemaApplicationResult(json)
    }

  @JSExportTopLevel("applyScroll")
  def applyScroll(): js.Array[String] = currentScroll match {
    case None =>
      dom.console.error("No current scroll")
      js.Array()
    case Some(scroll) =>
      scroll.applyToBackend() match {
        case Some(facts) =>
          facts.foreach(notifyUnity)
          facts.map(_.UPL_name).toJSArray
        case None =>
          dom.console.error("Schema application failed")
          js.Array()
      }
  }

  @JSExportTopLevel("refreshScrollView")
  def refreshScrollView(): Unit = Backend.refresh()


  def loadFiles(files: Map[String, Seq[(String, String)]]): Boolean = {
    val background = (files.getOrElse("background", Nil) ++ files.getOrElse("source", Nil)).map(_._2)
    UplSyntax.detect(background.mkString("\n"))
    val ok = Backend.loadLevel(files)
    FactRegistry.clear()
    currentScroll.foreach { s =>
      s.slots.foreach(_.assignedFact = None)
      s.results.foreach(_.fact = None)
    }
    ok
  }

  @JSExportTopLevel("loadLevel")
  def loadLevel(background: String, schemata: String, initialStage: js.UndefOr[String] = js.undefined): Boolean =
    loadFiles(Map(
      "background" -> Seq("Background" -> background),
      "schemata"   -> Seq("Schemata" -> schemata),
      "stageInit"  -> initialStage.toOption.filter(_.trim.nonEmpty).map("InitialStage" -> _).toSeq
    ))


  @JSExportTopLevel("loadLevelFromStrings")
  def loadLevelFromStrings(projectFile: String, files: js.Dictionary[String]): Boolean = {
    val entries = ProjectFile.parse(projectFile)
    val missing = entries.flatMap(_._2).filterNot(files.contains)
    if (missing.nonEmpty) {
      dom.console.error(s"Level files missing: ${missing.mkString(", ")}")
      false
    } else loadFiles(ProjectFile.collect(entries, files(_)))
  }


  @JSExportTopLevel("loadLevelFromProjectFile")
  def loadLevelFromProjectFile(url: String): js.Promise[Boolean] = {
    val ppUrl = new dom.URL(url, dom.document.baseURI).href
    def fetchText(u: String): Future[String] =
      dom.fetch(u).toFuture.flatMap { r =>
        if (r.ok) r.text().toFuture
        else Future.failed(new IllegalStateException(s"$u: HTTP ${r.status}"))
      }
    val result = for {
      pp <- fetchText(ppUrl)
      entries = ProjectFile.parse(pp)
      paths = entries.flatMap(_._2).distinct
      contents <- Future.traverse(paths)(p => fetchText(new dom.URL(p, ppUrl).href).map(p -> _))
    } yield loadFiles(ProjectFile.collect(entries, contents.toMap))
    result.recover { case NonFatal(e) =>
      dom.console.error(s"Could not load level from $url: ${e.getMessage}")
      false
    }.toJSPromise
  }


  object DemoLevel {
    val background: String =
      """type point
        |type triangle = (point,point,point)
        |dist: point -> point -> float
        |similar: triangle -> triangle -> bool""".stripMargin
    val schemata: String =
      """theory InterceptTheorem{
        |  _A: point
        |  _B: point
        |  _C: point
        |  _D: point
        |  _E: point
        |  _AB: float
        |  _AB_P: |- dist(_A)(_B) == _AB
        |  _AC: float
        |  _AC_P: |- dist(_A)(_C) == _AC
        |  _BE: float
        |  _BE_P: |- dist(_B)(_E) == _BE
        |  _are_similar: |- similar((_D,_A,_C))((_E,_A,_B))
        |  _CD = _AC * _BE / _AB
        |  _CD_P: |- dist(_C)(_D) == _CD = ???
        |}""".stripMargin
  }

  @JSExportTopLevel("loadDemoLevel")
  def loadDemoLevel(): Boolean = loadLevel(DemoLevel.background, DemoLevel.schemata)

  @JSExportTopLevel("helper")
  def helper(): Unit = currentScroll match {
    case None => dom.console.error("No current scroll")
    case Some(scroll) =>
      val points = List("_A" -> "ground", "_B" -> "q", "_C" -> "foot", "_D" -> "tip", "_E" -> "p")
      val dists = List(
        ("_AB", "ground_dist_small", "ground", "q", 42.0),
        ("_AC", "ground_dist_large", "ground", "foot", 420.0),
        ("_BE", "apparent_height", "q", "p", 21.0))

      val pointFacts = points.flatMap { case (slot, n) =>
        FactRegistry.declare(PointMeasurement(n, Some(n))).map(slot -> _)
      }
      val distFacts = dists.flatMap { case (slot, n, a, b, d) =>
        FactRegistry.declare(DistanceMeasurement(n, Some(n), a, b, d)).map(slot -> _)
      }
      val similar =
        FactRegistry.get("are_similar").orElse {
          if (Backend.add("are_similar: |- similar((tip,ground,foot))((p, ground, q)) = ???"))
            Some(FactRegistry.register(new AssertionFact("are_similar")))
          else None
        }.map("_are_similar" -> _).toList

      (pointFacts ++ distFacts ++ similar).foreach { case (slotName, fact) =>
        scroll.slots.find(_.UPL_name == slotName) match {
          case Some(slot) => slot.assignedFact = Some(fact)
          case None       => dom.console.warn(s"No slot named $slotName")
        }
      }
  }


  def htmlDecode(value: String): String = {
    val textarea = dom.document.createElement("textarea").asInstanceOf[dom.html.TextArea]
    textarea.innerHTML = value
    textarea.value
  }

  private val applyListener: js.Function1[dom.Event, Unit] = (_: dom.Event) => { applyScroll(); () }

  def init(): Unit = {
    def start(): Unit = {
      Option(dom.document.querySelector("#apply-scroll")).foreach(_.addEventListener("click", applyListener))
      val hasScroll = Option(dom.document.querySelector("#Unity-Data-Interface"))
        .exists(_.hasAttribute("data-scroll-dynamic"))
      Option(dom.document.body.getAttribute("data-level")).filter(_.nonEmpty) match {
        case Some(level) =>
          loadLevelFromProjectFile(level).toFuture.foreach(_ => if (hasScroll) renderScroll())
        case None =>
          if (hasScroll) renderScroll()
      }
    }
    if (dom.document.readyState.asInstanceOf[String] == "loading")
      dom.document.addEventListener("DOMContentLoaded", (_: dom.Event) => start())
    else start()
  }
}


object ProjectFile {

  def parse(content: String): List[(String, List[String])] =
    content.linesIterator.map(_.trim).filterNot(_.startsWith("//")).flatMap { line =>
      val i = line.indexOf(':')
      if (i <= 0) None
      else {
        val key = line.take(i).trim
        val files = line.drop(i + 1).trim.split("\\s+").filter(_.nonEmpty).toList
        if (key.nonEmpty && files.nonEmpty) Some(key -> files) else None
      }
    }.toList

  def collect(entries: List[(String, List[String])], read: String => String): Map[String, Seq[(String, String)]] =
    entries.foldLeft(Map.empty[String, Seq[(String, String)]]) { case (acc, (key, files)) =>
      acc.updated(key, acc.getOrElse(key, Seq.empty) ++ files.map(p => p -> read(p)))
    }
}

object ScrollViewMain {
  def main(args: Array[String]): Unit = {
    DropFacts.init()
    SetScrollContent.init()
  }
}
