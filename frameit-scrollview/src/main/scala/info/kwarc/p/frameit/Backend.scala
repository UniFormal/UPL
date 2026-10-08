package info.kwarc.p.frameit

import info.kwarc.p.{FrameITProject, FrameIT_Backend, SourceOrigin}
import com.raquo.airstream.core.Signal
import com.raquo.airstream.state.Var
import org.scalajs.dom

import scala.collection.immutable.ListMap
import scala.util.Try

final case class ValueFactData(func: String, args: List[String], value: Double)


object Backend {

  private def project: FrameITProject = FrameIT_Backend.proj
  private def lowo = project.LoWo

  private val revisionVar: Var[Int] = Var(0)

  val revision: Signal[Int] = revisionVar.signal

  def refresh(): Unit = revisionVar.update(_ + 1)

  private def guarded[A](what: String)(body: => A): Option[A] =
    Try(body).toOption.orElse {
      dom.console.error(s"UPL-Aufruf fehlgeschlagen: $what")
      None
    }

  private def write(what: String)(body: => Boolean): Boolean = {
    val ok = guarded(what)(body).getOrElse(false)
    if (ok) refresh()
    else dom.console.warn(s"UPL hat abgelehnt: $what\n$errors")
    ok
  }


  def loadLevel(files: Map[String, Seq[(String, String)]]): Boolean = {
    val contents = files.map { case (key, fs) =>
      key -> fs.map { case (path, text) => (SourceOrigin(path), text) }
    }
    val ok = guarded("loadLevel") {
      val p = FrameITProject(contents)
      FrameIT_Backend.proj = p
      !p.hasErrors
    }.getOrElse(false)
    refresh()
    if (!ok) dom.console.warn(s"Level enthält Fehler:\n${allErrors}")
    ok
  }


  def add(decls: String): Boolean = write(s"add($decls)")(lowo.add(decls))

  def resetLevel(): Unit = { guarded("resetLevel")(lowo.reset()); refresh() }

  def applySchema(schema: String,
                  required: Seq[(String, String)],
                  results: Seq[(String, String)]): Boolean =
    write(s"applySchema($schema)")(project.applySchema(schema, ListMap(required: _*), ListMap(results: _*)))


  def lookupNum(name: String): Option[Double] =
    guarded(s"lookupNum($name)")(lowo.lookupNum(name)).flatten

  def lookupValueFact(name: String): Option[ValueFactData] =
    guarded(s"lookupValueFact($name)")(lowo.lookupValueFact(name)).flatten.map {
      case (func, args, value) => ValueFactData(func.toString.stripPrefix("."), args.map(_.toString), value)
    }

  def eval(expr: String): Option[String] =
    guarded(s"eval($expr)")(lowo.evalTyped(expr)).flatten.map(_._1.toString)

  def errors: String = guarded("errors")(lowo.errors.toString).getOrElse("")
  def allErrors: String = guarded("allErrors")(project.getErrors.mkString("\n")).getOrElse("")
}
