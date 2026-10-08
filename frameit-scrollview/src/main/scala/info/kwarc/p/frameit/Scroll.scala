package info.kwarc.p.frameit

import org.scalajs.dom
import com.raquo.airstream.core.Signal
import com.raquo.airstream.state.Var
import com.raquo.airstream.ownership.Owner


private final class KillableOwner extends Owner {
  def kill(): Unit = killSubscriptions()
}


private final class ViewBinding(attr: String, id: String) {
  private var owner = new KillableOwner
  val selector: String = s"[$attr='$id']"

  def bind[A](signal: Signal[A])(render: (dom.Element, A) => Unit): Unit = {
    owner.kill()
    owner = new KillableOwner
    signal.foreach(a => DomUtil.forEachElement(selector)(render(_, a)))(owner)
  }
}

private object Describe {
  def apply(f: Fact): String = f match {
    case v: ValueFact => v.value.fold(v.UPL_name)(x => s"${v.UPL_name} = $x")
    case other        => other.UPL_name
  }
}


class Slot(uri: String, `type`: String, name: Option[String] = None)
    extends BackendObject(uri, `type`, name) {

  private val assigned: Var[Option[Fact]] = Var(None)
  private val view = new ViewBinding("data-slot-id", uri)

  def assignedFact: Option[Fact] = assigned.now()
  def assignedFact_=(fact: Option[Fact]): Unit = assigned.set(fact)

  def defaultLabel: dom.Element = super.label
  override def label: dom.Element = assignedFact.fold(defaultLabel)(_.label)

  def accepts(f: Fact): Boolean = {
    val allowed = `type`.split(" ").filter(_.nonEmpty)
    allowed.isEmpty || allowed.exists(f.fits)
  }

  def prepare(): Unit = {
    DomUtil.forEachElement(view.selector) { el =>
      el.setAttribute("dropzone", "copy")
      el.setAttribute("data-allowed-types", `type`)
    }
    view.bind(assigned.signal.combineWith(Backend.revision)) { case (el, (factOpt, _)) =>
      DomUtil.setContent(el, label)
      factOpt match {
        case Some(f) =>
          el.setAttribute("data-fact-id", f.uri)
          el.setAttribute("title", Describe(f))
        case None =>
          el.removeAttribute("data-fact-id")
          el.removeAttribute("title")
      }
    }
  }
}


final class ResultView(val ref: BackendObject) {
  private val produced: Var[Option[Fact]] = Var(None)
  private val view = new ViewBinding("data-solution-id", ref.uri)

  def fact: Option[Fact] = produced.now()
  def fact_=(f: Option[Fact]): Unit = produced.set(f)

  def prepare(): Unit =
    view.bind(produced.signal.combineWith(Backend.revision)) { case (el, (factOpt, _)) =>
      DomUtil.setContent(el, factOpt.fold(ref.label)(_.label))
      el.setAttribute("data-allowed-types", ref.`type`)
      factOpt match {
        case Some(f) => el.setAttribute("data-fact-id", f.uri); el.setAttribute("title", Describe(f))
        case None    => el.removeAttribute("data-fact-id"); el.removeAttribute("title")
      }
    }
}


class Scroll(
  uri: String,
  val slots: List[Slot],
  val resultingFacts: List[BackendObject],
  val description: dom.Element,
  name: Option[String] = None,
  val depiction: Option[dom.Element] = None
) extends BackendObject(uri, "Scroll", name) {

  val results: List[ResultView] = resultingFacts.map(new ResultView(_))

  def render(): Unit = {
    if (uri != SetScrollContent.lastScrollUri) {
      SetScrollContent.lastScrollUri = uri
      DomUtil.setContentBySelector("#scroll-label", label)
    }
    slots.foreach(_.prepare())
    results.foreach(_.prepare())
    dom.console.log("Scroll rendered", UPL_name)
    DropFacts.addDropZoneEventListeners()
  }

  private def freshName(schemaName: String): String = {
    val base = schemaName.stripPrefix("_")
    Iterator.from(1).map(i => if (i == 1) base else s"${base}_$i")
      .find(n => !FactRegistry.nameTaken(n)).get
  }

  private def factFromUpl(newName: String): Option[Fact] =
    Backend.lookupValueFact(newName) match {
      case Some(ValueFactData(func, List(a, b), _)) if func.endsWith("dist") =>
        Some(new LineSegmentFact(newName, a, b, Some(newName)))
      case Some(ValueFactData(func, List(a, b, c), _)) if func.endsWith("angle") =>
        Some(new AngleFact(newName, a, b, c, Some(newName)))
      case Some(ValueFactData(func, _, _)) =>
        Some(new ValueFact(newName, func, Some(newName)))
      case None if Backend.lookupNum(newName).isDefined =>
        Some(new ValueFact(newName, "value", Some(newName)))
      case None =>
        dom.console.warn(s"Ergebnis $newName ist in UPL nicht als Wert auffindbar")
        None
    }

  def applyToBackend(): Option[List[Fact]] = {
    val unassigned = slots.filter(_.assignedFact.isEmpty).map(_.UPL_name)
    if (unassigned.nonEmpty) dom.console.warn(s"Nicht belegte Slots: ${unassigned.mkString(", ")}")

    val required = slots.flatMap { s =>
      s.assignedFact.toList.flatMap {
        case v: ValueFact => List(s.UPL_name -> v.UPL_name, s"${s.UPL_name}_P" -> s"${v.UPL_name}_P")
        case f            => List(s.UPL_name -> f.UPL_name)
      }
    }
    val names = resultingFacts.map(r => r.UPL_name -> freshName(r.UPL_name))
    val acquired = names.flatMap { case (r, n) => List(r -> n, s"${r}_P" -> s"${n}_P") }

    if (!Backend.applySchema(UPL_name, required, acquired)) None
    else {
      val facts = results.zip(names).flatMap { case (view, (_, n)) =>
        val f = factFromUpl(n).map(FactRegistry.register)
        view.fact = f
        f
      }
      Some(facts)
    }
  }
}


object DomUtil {
  def forEachElement(selector: String)(f: dom.Element => Unit): Unit = {
    val nodes = dom.document.querySelectorAll(selector)
    for (i <- 0 until nodes.length) f(nodes(i))
  }

  def setContent(container: dom.Element, content: dom.Element): Unit = {
    container.innerHTML = ""
    container.appendChild(content.cloneNode(true))
  }

  def setContentBySelector(selector: String, content: dom.Element): Unit =
    Option(dom.document.querySelector(selector)).foreach(setContent(_, content))
}
