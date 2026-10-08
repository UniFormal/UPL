package info.kwarc.p.frameit

import org.scalajs.dom
import scala.scalajs.js
import scala.collection.mutable


object ApiParser {

  private val primitives = Set("string", "MathMLElement", "HTMLElement", "SVGElement")

  private lazy val parser = js.Dynamic.newInstance(js.Dynamic.global.DOMParser)()

  private def typeError(msg: String): Nothing =
    throw js.JavaScriptException(new js.TypeError(msg))

  private def parse(s: String): dom.Element = {
    val doc = parser.parseFromString(s, "text/html")
    val first = doc.body.firstElementChild
    if (first == null) typeError(s"Markup contains no element: $s")
    first.asInstanceOf[dom.Element]
  }

  private def isObject(x: js.Any): Boolean = x != null && js.typeOf(x) == "object"

  private def isPrimitive(member: js.Dynamic): Boolean =
    isObject(member) &&
      js.typeOf(member.parseAs) == "string" &&
      primitives.contains(member.parseAs.asInstanceOf[String]) &&
      js.typeOf(member.content) == "string"


  def backendObjectFromJson(jsonObject: js.Dynamic): BackendObject = {
    if (!isObject(jsonObject)) typeError(s"Expected a JSON object, got: $jsonObject")
    val bo = mutable.Map.empty[String, Any]

    js.Object.keys(jsonObject.asInstanceOf[js.Object]).foreach { key =>
      val member = jsonObject.selectDynamic(key)
      if (isPrimitive(member)) {
        val content = member.content.asInstanceOf[String]
        member.parseAs.asInstanceOf[String] match {
          case "string" => bo(key) = content
          case _        => bo(key) = parse(content)
        }
      } else if (js.Array.isArray(member)) {
        val values = member.asInstanceOf[js.Array[js.Dynamic]].toList
        bo(key) = if (key == "slots") values.map(slotFromJson) else values.map(backendObjectFromJson)
      } else if (isObject(member)) {
        bo(key) = backendObjectFromJson(member)
      } else {
        bo(key) = member
      }
    }

    def requireString(key: String): String = bo.get(key) match {
      case Some(s: String) => s
      case other =>
        dom.console.error(s"Attribute '$key': $other is missing or not a string. Cannot finish parsing", jsonObject)
        typeError(s"Attribute '$key' is missing or not a string")
    }
    val uri = requireString("uri")
    val tpe = requireString("type")

    tpe match {
      case "Scroll" =>
        new Scroll(
          uri,
          slots = listOf[Slot](bo.get("slots")),
          resultingFacts = listOf[BackendObject](bo.get("resultingFacts")),
          description = element(bo.get("description")).getOrElse(dom.document.createElement("div")),
          name = bo.get("name").collect { case s: String => s },
          depiction = element(bo.get("depiction"))
        )
      // @todo weitere Fälle ergänzen
      case _ => new PureReference(uri, tpe)
    }
  }

  private def listOf[A](v: Option[Any]): List[A] = v match {
    case Some(l: List[_]) => l.asInstanceOf[List[A]]
    case _                => Nil
  }

  private def element(v: Option[Any]): Option[dom.Element] = v.collect { case e: dom.Element => e }

  def slotFromJson(jsonSlot: js.Dynamic): Slot = {
    val sl = backendObjectFromJson(jsonSlot)
    new Slot(sl.uri, sl.`type`)
  }


  private def str(o: js.Dynamic, key: String): Option[String] = {
    val v = o.selectDynamic(key)
    if (js.typeOf(v) == "string") Some(v.asInstanceOf[String]) else None
  }
  private def num(o: js.Dynamic, key: String): Option[Double] = {
    val v = o.selectDynamic(key)
    if (js.typeOf(v) == "number") Some(v.asInstanceOf[Double]) else None
  }


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

  def idOf(serialized: String): Option[String] =
    scala.util.Try(js.JSON.parse(serialized)).toOption.filter(isObject).flatMap(str(_, "id"))
}
