package info.kwarc.p.frameit

import org.scalajs.dom
import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel
import scala.util.control.NonFatal


object DropFacts {

  private def slotFor(el: dom.Element): Option[Slot] =
    for {
      slotId <- Option(el.getAttribute("data-slot-id"))
      scroll <- SetScrollContent.currentScroll
      slot   <- scroll.slots.find(_.uri == slotId)
    } yield slot

  private def factFromDragData(data: String): Option[Fact] =
    ApiParser.idOf(data).flatMap(FactRegistry.get).orElse {
      try FactRegistry.declare(ApiParser.parseMeasurement(data))
      catch {
        case NonFatal(e) =>
          dom.console.error("Could not parse dropped fact", e.getMessage, data)
          None
      }
    }

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

  @JSExportTopLevel("declareMeasuredFact")
  def declareMeasuredFact(serializedFact: String): Boolean =
    try FactRegistry.declare(ApiParser.parseMeasurement(serializedFact)).isDefined
    catch {
      case NonFatal(e) =>
        dom.console.error("Could not declare measured fact", e.getMessage, serializedFact)
        false
    }

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

  def addDropZoneEventListeners(): Unit =
    DomUtil.forEachElement("""[dropzone="copy"]""") { el =>
      el.removeEventListener("drop", dropListener)
      el.removeEventListener("mousedown", clickListener)
      el.removeEventListener("contextmenu", contextMenuListener)
      el.addEventListener("drop", dropListener)
      el.addEventListener("mousedown", clickListener)
      el.addEventListener("contextmenu", contextMenuListener)
    }

  def init(): Unit = dom.document.addEventListener("dragover", dragOverListener)
}
