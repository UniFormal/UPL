package info.kwarc.p.frameit

import info.kwarc.p.{FrameITProject, FrameIT_Backend, SourceOrigin}
import com.raquo.airstream.core.Signal
import com.raquo.airstream.state.Var
import org.scalajs.dom

import scala.collection.immutable.ListMap
import scala.util.Try

final case class ValueFactData(func: String, args: List[String], value: Double)

// The ScrollView is built together with UPL into a single Scala.js program and therefore
// calls UPL directly in Scala with real types.

object Backend {

  // "def" instead of "val": loading a level creates a new project, so the current one
  // has to be read again on every call. A "val" would keep the old project
  private def project: FrameITProject = FrameIT_Backend.proj
  private def lowo = project.LoWo

  // Counts the changes to the logical world...
  private val revisionVar: Var[Int] = Var(0)

  // ...while the outside only gets the read-only signal. Views observe it
  val revision: Signal[Int] = revisionVar.signal

  // Tells all views that UPL has changed
  def refresh(): Unit = revisionVar.update(_ + 1)

  // Runs a UPL call and turns an exception into "None"
  private def guarded[A](what: String)(body: => A): Option[A] =
    Try(body).toOption.orElse {
      dom.console.error(s"UPL-Aufruf fehlgeschlagen: $what")
      None
    }

  // Runs a changing UPL call
  // On success, "revision" is increased so that all views are updated
  // On failure, UPLs error messages are logged
  private def write(what: String)(body: => Boolean): Boolean = {
    val ok = guarded(what)(body).getOrElse(false)
    if (ok) refresh()
    else dom.console.warn(s"UPL hat abgelehnt: $what\n$errors")
    ok
  }

  // Loads a level
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


  // Adds declarations to the logical world, e.g. "p: point = ???"
  def add(decls: String): Boolean = write(s"add($decls)")(lowo.add(decls))

  // Resets the logical world to the initial state of the level
  def resetLevel(): Unit = { guarded("resetLevel")(lowo.reset()); refresh() }

  // Applies a schema (scroll)
  def applySchema(schema: String,
                  required: Seq[(String, String)],
                  results: Seq[(String, String)]): Boolean =
    write(s"applySchema($schema)")(project.applySchema(schema, ListMap(required: _*), ListMap(results: _*)))


  // Numeric value of a constant, e.g. 42 for "ground_dist_small"
  def lookupNum(name: String): Option[Double] =
    guarded(s"lookupNum($name)")(lowo.lookupNum(name)).flatten

  def lookupValueFact(name: String): Option[ValueFactData] =
    guarded(s"lookupValueFact($name)")(lowo.lookupValueFact(name)).flatten.map {
      case (func, args, value) => ValueFactData(func.toString.stripPrefix("."), args.map(_.toString), value)
    }

  // Evaluates an expression in the logical world and returns the result as text
  def eval(expr: String): Option[String] =
    guarded(s"eval($expr)")(lowo.evalTyped(expr)).flatten.map(_._1.toString)

  // Error messages of the last change to the logical world
  def errors: String = guarded("errors")(lowo.errors.toString).getOrElse("")
  // All error messages of the project (level files and the logical world)
  def allErrors: String = guarded("allErrors")(project.getErrors.mkString("\n")).getOrElse("")
}
