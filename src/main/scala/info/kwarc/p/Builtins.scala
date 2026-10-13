package info.kwarc.p

import scala.io.StdIn.readLine

class Uniformal(ip: Interpreter) {
  def print(as: List[Expression]): Expression = as.head match {
    case StringValue(v) => println(v); Unit.Value
    case s => ip.fail("not a string")(s)
  }
  def read(): Expression = {
    val s = readLine()
    StringValue(s)
  }





}