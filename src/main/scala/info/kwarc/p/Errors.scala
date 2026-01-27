package info.kwarc.p

/** parent of all errors */
abstract class PError(msg: String) extends Exception(msg) {
  override def toString = "error: " + msg
}

/** user error in source */
abstract class SError(val loc: Location, msg: String) extends PError(msg) {
  override def toString = "error at " + loc + ":" + msg
}

/** implementation errors */
case class IError(msg: String) extends PError(msg)

/** thrown by AST code that has no state to recover from an error; should be caught and transformed into PError by other components */
case class ASTError(msg: String) extends PError(msg)

abstract class ErrorHandler {
  def apply(e: SError): Unit
  def size = 0
}

object ErrorThrower extends ErrorHandler {
  def apply(e: SError) = throw e
}

object ErrorIgnorer extends ErrorHandler {
  def apply(e: SError) = {}
}

class ErrorCollector extends ErrorHandler {
  override def toString = getErrors.mkString("\n")
  private var errors: List[SError] = Nil
  override def size = errors.length
  def hasErrors = errors.nonEmpty
  def getErrors = errors.reverse
  def apply(e: SError) = {
    if (e.loc == null) throw IError(s"SError without valid Location: ${e.getMessage}")
    errors ::= e
    val errO: Option[SError] = Option {
      if (errors.count(_ == e) >= 10) HandlerError(e.loc, "The exact same error has been reported 10 times. Loop suspected.")
      else if (errors.size > 1000) HandlerError(e.loc, "Exceeded 1000 errors. Giving up.")
      else null
    }
    errO.foreach { err => errors ::= err; throw err }
  }
  def clear = {errors = Nil}
  case class HandlerError(l: Location, msg: String) extends SError(l, msg)
}

trait ThrowsErrors {
  val errorHandler: ErrorHandler
  val operation: String
  case class Error(cause: SyntaxFragment, msg: String) extends SError(cause.loc, s"$msg while $operation $cause")
  def reportError(msg: String)(implicit cause: SyntaxFragment) = {
    val e = Error(cause, msg)
    errorHandler(e)
  }
}
