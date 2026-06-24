package info.kwarc.p

class Uniformal(ip: Interpreter) {
  def print(as: List[Expression]): Expression = as.head match {
    case StringValue(v) => println(v); Unit.Value
    case s => ip.fail("not a string")(s)
  }
}