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
  def hasErrors = errors.nonEmpty
  def getErrors = errors.reverse
  def apply(e: SError) = {
    if (e.loc == null) throw IError(s"SError without valid Location. Original error message:\n$e")
    errors ::= e
  }
  def clear = {errors = Nil}
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
