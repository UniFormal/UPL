package info.kwarc.p.frameit

import org.scalajs.dom
import scala.scalajs.js
import scala.collection.mutable


object ApiParser {

  // Port of API_Parser. Reads two JSON formats
  // 1. Scroll descriptions
  // 2. Facts from Unity

  // Values of "parseAs" that wrap a primitive value
  // To support another type add it here and handle it in backendObjectFromJson
  private val primitives = Set("string", "MathMLElement", "HTMLElement", "SVGElement")

  // The browsers DOMParser, created on first use = lazy
  private lazy val parser = js.Dynamic.newInstance(js.Dynamic.global.DOMParser)()

  private def typeError(msg: String): Nothing =
    throw js.JavaScriptException(new js.TypeError(msg))

  // Parses a markup string (MathML, HTML or SVG) and returns its first element
  private def parse(s: String): dom.Element = {
    val doc = parser.parseFromString(s, "text/html")
    val first = doc.body.firstElementChild
    if (first == null) typeError(s"Markup contains no element: $s")
    first.asInstanceOf[dom.Element]
  }

  // x a JavaScript object and not null?
  private def isObject(x: js.Any): Boolean = x != null && js.typeOf(x) == "object"

  // Is member a wrapped primitive value of the form { parseAs: <known type>, content: <string> }?
  private def isPrimitive(member: js.Dynamic): Boolean =
    isObject(member) &&
      js.typeOf(member.parseAs) == "string" &&
      primitives.contains(member.parseAs.asInstanceOf[String]) &&
      js.typeOf(member.content) == "string"

  // Scroll descriptions begins
  // Turns a scroll description or a part of it into a BackendObject
  def backendObjectFromJson(jsonObject: js.Dynamic): BackendObject = {
    if (!isObject(jsonObject)) typeError(s"Expected a JSON object, got: $jsonObject")
    // Collects all fields of the object, already converted
    val bo = mutable.Map.empty[String, Any]

    js.Object.keys(jsonObject.asInstanceOf[js.Object]).foreach { key =>
      val member = jsonObject.selectDynamic(key)
      if (isPrimitive(member)) {
        // Wrapped value: Unwrap the content according to parseAs
        val content = member.content.asInstanceOf[String]
        member.parseAs.asInstanceOf[String] match {
          case "string" => bo(key) = content
          case _        => bo(key) = parse(content)
        }
      } else if (js.Array.isArray(member)) {
        // An array, which converts every element; entries under "slots" become Slots
        val values = member.asInstanceOf[js.Array[js.Dynamic]].toList
        bo(key) = if (key == "slots") values.map(slotFromJson) else values.map(backendObjectFromJson)
      } else if (isObject(member)) {
        bo(key) = backendObjectFromJson(member)
      } else {
        bo(key) = member
      }
    }

    // Every BackendObject needs "uri" and "type" as strings
    // Otherwise parsing fails
    def requireString(key: String): String = bo.get(key) match {
      case Some(s: String) => s
      case other =>
        dom.console.error(s"Attribute '$key': $other is missing or not a string. Cannot finish parsing", jsonObject)
        typeError(s"Attribute '$key' is missing or not a string")
    }
    val uri = requireString("uri")
    val tpe = requireString("type")

    // Build the matching object depending on "type"
    tpe match {
      case "Scroll" =>
        new Scroll(
          uri,
          slots = listOf[Slot](bo.get("slots")),
          resultingFacts = listOf[BackendObject](bo.get("resultingFacts")),
          // Empty element instead of failing
          description = element(bo.get("description")).getOrElse(dom.document.createElement("div")),
          name = bo.get("name").collect { case s: String => s },
          depiction = element(bo.get("depiction"))
        )
      // @todo add further cases
      case _ => new PureReference(uri, tpe)
    }
  }

  // The value as a list of "A" or an empty list if it is missing or not a list
  private def listOf[A](v: Option[Any]): List[A] = v match {
    case Some(l: List[_]) => l.asInstanceOf[List[A]]
    case _                => Nil
  }

  // The value as a DOM element, if it is one
  private def element(v: Option[Any]): Option[dom.Element] = v.collect { case e: dom.Element => e }

  // Reads a slot
  // Name and label are derived from the uri
  def slotFromJson(jsonSlot: js.Dynamic): Slot = {
    val sl = backendObjectFromJson(jsonSlot)
    new Slot(sl.uri, sl.`type`)
  }


  // Facts from Unity begins here

  // The field "key" of "o" if it is a string
  private def str(o: js.Dynamic, key: String): Option[String] = {
    val v = o.selectDynamic(key)
    if (js.typeOf(v) == "string") Some(v.asInstanceOf[String]) else None
  }

  // The field "key" of "o" if it is a number
  private def num(o: js.Dynamic, key: String): Option[Double] = {
    val v = o.selectDynamic(key)
    if (js.typeOf(v) == "number") Some(v.asInstanceOf[Double]) else None
  }


  // Reads a fact serialized by Unity
  // {"s_type": "PointFact", "id": ..., "label": ...}
  // { "s_type": "LineFact",  "id": ..., "label": ..., "pid1": ..., "pid2": ..., "distance": ... }
  // The result is not yet known to UPL; FactRegistry.declare declares it
  def parseMeasurement(serialized: String): Measurement = {
    val parsed = js.JSON.parse(serialized)
    if (!isObject(parsed)) typeError(s"Couldn't parse $serialized to a fact")
    val m: Option[Measurement] = str(parsed, "s_type") match {
      case Some("PointFact") =>
        str(parsed, "id").map(PointMeasurement(_, str(parsed, "label")))
      case Some("LineFact") =>
        for {
          id   <- str(parsed, "id")
          pid1 <- str(parsed, "pid1")
          pid2 <- str(parsed, "pid2")
          d    <- num(parsed, "distance")
        } yield DistanceMeasurement(id, str(parsed, "label"), pid1, pid2, d)
      case _ => None
    }
    m.getOrElse(typeError(s"Couldn't parse $serialized to a fact"))
  }

  // Only Unitiys id of a serialized fact without checking the rest
  // Used by DropFacts to look up an already known fact in the FactRegistry
  def idOf(serialized: String): Option[String] =
    scala.util.Try(js.JSON.parse(serialized)).toOption.filter(isObject).flatMap(str(_, "id"))
}
