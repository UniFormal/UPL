package info.kwarc.p.frameit

import org.scalajs.dom
import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel
import scala.util.control.NonFatal

// The interaction layer

object DropFacts {

  // The slot an element of the page stands for
  // "None" if the element has no "data-slot-id", no scroll is shown or the scroll ha no such slot
  private def slotFor(el: dom.Element): Option[Slot] =
    for {
      slotId <- Option(el.getAttribute("data-slot-id"))
      scroll <- SetScrollContent.currentScroll
      slot   <- scroll.slots.find(_.uri == slotId)
    } yield slot

  // The fact belonging to the drag data: if its id is already known, the existing fact
  // from the registry; otherwise the data is parsed as a measurement and declared in UPL
  private def factFromDragData(data: String): Option[Fact] =
    ApiParser.idOf(data).flatMap(FactRegistry.get).orElse {
      try FactRegistry.declare(ApiParser.parseMeasurement(data))
      catch {
        case NonFatal(e) =>
          dom.console.error("Could not parse dropped fact", e.getMessage, data)
          None
      }
    }

  // Called when the player drops a fact on a slot
  // The fact is assigned only if it fits the slot's type
  // The view then updates itself; benifit of using Airstream
  def dropFactHandler(event: dom.DragEvent): Unit =
    (event.currentTarget, Option(event.dataTransfer)) match {
      case (target: dom.Element, Some(transfer)) =>
        event.preventDefault()
        for {
          slot <- slotFor(target)
          fact <- factFromDragData(transfer.getData("application/json"))
        } {
          if (slot.accepts(fact)) slot.assignedFact = Some(fact)
          else dom.console.warn(
            s"The dropped fact '${fact.UPL_name}' does not fit slot '${slot.UPL_name}' (expects '${slot.`type`}')")
        }
      case _ =>
        dom.console.log("Ignored illegal DragEvent")
    }

  // Called by Unity when a measurement has produced a new fact
  @JSExportTopLevel("declareMeasuredFact")
  def declareMeasuredFact(serializedFact: String): Boolean =
    try FactRegistry.declare(ApiParser.parseMeasurement(serializedFact)).isDefined
    catch {
      case NonFatal(e) =>
        dom.console.error("Could not declare measured fact", e.getMessage, serializedFact)
        false
    }

  // Handles mouse clicks on a slot
  def clickHandler(event: dom.MouseEvent): Unit =
    event.currentTarget match {
      case target: dom.Element =>
        event.preventDefault()
        slotFor(target).foreach { slot =>
          event.button.toInt match {
            case 0 => ()
            case 1 => ()
            case 2 => slot.assignedFact = None
            case _ => dom.console.log("Button has no effect")
          }
        }
      case _ =>
        dom.console.warn("Ignored illegal ClickEvent")
    }

  private val dropListener: js.Function1[dom.DragEvent, Unit] = (e: dom.DragEvent) => dropFactHandler(e)
  private val clickListener: js.Function1[dom.MouseEvent, Unit] = (e: dom.MouseEvent) => clickHandler(e)
  private val contextMenuListener: js.Function1[dom.Event, Unit] = (e: dom.Event) => e.preventDefault()
  private val dragOverListener: js.Function1[dom.Event, Unit] = (e: dom.Event) => e.preventDefault()

  // Registers the listeners on all drop zones, each exactly once
  def addDropZoneEventListeners(): Unit =
    DomUtil.forEachElement("""[dropzone="copy"]""") { el =>
      el.removeEventListener("drop", dropListener)
      el.removeEventListener("mousedown", clickListener)
      el.removeEventListener("contextmenu", contextMenuListener)
      el.addEventListener("drop", dropListener)
      el.addEventListener("mousedown", clickListener)
      el.addEventListener("contextmenu", contextMenuListener)
    }

  // Called once at startup
  // Allows dropping anywhere in the document
  def init(): Unit = dom.document.addEventListener("dragover", dragOverListener)
}
