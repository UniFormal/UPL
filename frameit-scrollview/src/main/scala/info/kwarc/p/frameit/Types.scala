package info.kwarc.p.frameit

import org.scalajs.dom
import scala.collection.mutable


object MathML {
  val Namespace = "http://www.w3.org/1998/Math/MathML"

  def elem(tag: String, children: dom.Node*): dom.Element = {
    val el = dom.document.createElementNS(Namespace, tag)
    children.foreach(el.appendChild)
    el
  }

  def textElem(tag: String, text: String): dom.Element =
    elem(tag, dom.document.createTextNode(text))

  def mrow(children: dom.Node*): dom.Element = elem("mrow", children: _*)
  def mo(text: String): dom.Element    = textElem("mo", text)
  def mn(text: String): dom.Element    = textElem("mn", text)
  def mi(text: String): dom.Element    = textElem("mi", text)
  def mtext(text: String): dom.Element = textElem("mtext", text)

  def mathMLify(s: String): dom.Element = mi(s)
  def mathMLify(d: Double): dom.Element = mn(d.toString)

  def unknown: dom.Element = mi("?")
}

import MathML._


abstract class BackendObject(val uri: String, val `type`: String, name: Option[String] = None) {

  val UPL_name: String = name.getOrElse(uri.split("\\?", -1).last)

  def label: dom.Element = mathMLify(UPL_name)
}

class PureReference(uri: String, `type`: String = "none") extends BackendObject(uri, `type`)

abstract class Fact(uri: String, `type`: String, name: Option[String])
    extends BackendObject(uri, `type`, name) {

  def s_type: Option[String] = None

  def uplType: String

  def fits(allowed: String): Boolean =
    s_type.contains(allowed) || uplType == allowed || `type` == allowed

  protected def defaultHint: String = "name"

  def show(hint: String): dom.Element = label
  final def show(): dom.Element = show(defaultHint)
}

class PointFact(uri: String, name: Option[String] = None) extends Fact(uri, "point", name) {
  override def s_type: Option[String] = Some("PointFact")
  def uplType = "point"
}

class Known3DPointFact(uri: String, name: Option[String] = None)
    extends Fact(uri, "Known3DPoint", name) {
  def uplType = "Known3DPoint"
  override protected def defaultHint = "value"
  override def show(hint: String): dom.Element = hint match {
    case "value" => Backend.eval(UPL_name).map(mtext).getOrElse(unknown)
    case _       => label
  }
}

class ValueFact(uri: String, val func: String, name: Option[String] = None)
    extends Fact(uri, func, name) {
  def uplType = "float"

  def value: Option[Double] = Backend.lookupNum(UPL_name)
  def data: Option[ValueFactData] = Backend.lookupValueFact(UPL_name)

  override def show(hint: String): dom.Element = hint match {
    case "value" => value.map(mathMLify).getOrElse(unknown)
    case "detailed" =>
      data match {
        case Some(ValueFactData(f, args, v)) =>
          val argNodes: List[dom.Node] = args.flatMap(a => List(mi(a), mo(","))).dropRight(1)
          mrow((List[dom.Node](mi(f), mo("(")) ++ argNodes ++ List(mo(")"), mo("="), mathMLify(v))): _*)
        case None => unknown
      }
    case _ => label
  }
}

class AssertionFact(uri: String, name: Option[String] = None) extends Fact(uri, "assertion", name) {
  def uplType = "assertion"
}

class AngleFact(uri: String, val p1: String, val p2: String, val p3: String, name: Option[String] = None)
    extends ValueFact(uri, "angle", name) {
  def isRightAngle: Boolean = value.contains(90.0)
}

class LineSegmentFact(uri: String, val p1: String, val p2: String, name: Option[String] = None)
    extends ValueFact(uri, "dist", name) {
  override def s_type: Option[String] = Some("LineFact")
  override protected def defaultHint = "value"
  def length: Option[Double] = value
}

class LineFact(uri: String, val p1: String, val p2: String, name: Option[String] = None,
               `type`: String = "Line_Fact")
    extends Fact(uri, `type`, name) {
  def uplType = "line"
  override protected def defaultHint = "Semantics"
  override def show(hint: String): dom.Element = hint match {
    case "Semantics" => mrow(mtext("The Line through "), mi(p1), mtext(" and "), mi(p2))
    case "Point vector" | "Parametric equation" | "Hesse normal form" =>
      throw new NotImplementedError("Not implemented.")
    case _ => label
  }
}

class RayFact(uri: String, p1: String, p2: String, name: Option[String] = None)
    extends LineFact(uri, p1, p2, name, "Ray_Fact")



object UplSyntax {
  var curried: Boolean = true

  def apply(func: String, args: String*): String =
    if (curried) func + args.map(a => s"($a)").mkString
    else args.mkString(s"$func(", ", ", ")")

  def detect(background: String, func: String = "dist"): Unit = {
    val tupled = raw"(^|\s)$func\s*:\s*\(".r
    curried = !background.linesIterator.exists(l => tupled.findFirstIn(l).isDefined)
  }
}


sealed trait Measurement { def id: String; def label: Option[String] }
final case class PointMeasurement(id: String, label: Option[String]) extends Measurement
final case class DistanceMeasurement(id: String, label: Option[String],
                                     pid1: String, pid2: String, distance: Double) extends Measurement


object FactRegistry {
  private val byId = mutable.LinkedHashMap.empty[String, Fact]

  def get(id: String): Option[Fact] = byId.get(id)
  def byUplName(name: String): Option[Fact] = byId.values.find(_.UPL_name == name)
  def register(f: Fact): Fact = { byId(f.uri) = f; f }
  def clear(): Unit = byId.clear()

  private def uplNameOf(id: String): Option[String] = byId.get(id).map(_.UPL_name)

  def nameTaken(name: String): Boolean = byUplName(name).isDefined

  def declare(m: Measurement): Option[Fact] = get(m.id).orElse {
    val name = m.label.filter(_.nonEmpty).getOrElse(m.id)
    m match {
      case PointMeasurement(id, _) =>
        if (Backend.add(s"$name: point = ???")) Some(register(new PointFact(id, Some(name)))) else None

      case DistanceMeasurement(id, _, pid1, pid2, distance) =>
        (uplNameOf(pid1), uplNameOf(pid2)) match {
          case (Some(a), Some(b)) =>
            val decl = s"$name = $distance\n${name}_P : |- ${UplSyntax("dist", a, b)} == $name = ???"
            if (Backend.add(decl)) Some(register(new LineSegmentFact(id, a, b, Some(name)))) else None
          case _ =>
            dom.console.warn(s"Strecke $id: Endpunkte $pid1/$pid2 sind nicht angemeldet")
            None
        }
    }
  }
}
