package info.kwarc.p

object Test {
  def mustFail[A, E <: PError](cls: Class[E])(code: => A): Any = {
    try {
      code
    }
    catch {
      case e: PError if e.getClass == cls =>
      case e : PError => println("test failed unexpected error "+ e)
    }
  }

  def parse(s: String): TheoryValue = Parser.text(SourceOrigin("test"), s, ErrorThrower)

  def check(s: String): TheoryValue = {
    val v = parse(s)
    new Checker(ErrorThrower).checkVocabulary(GlobalContext("test"), v, keepFull = true)(v)
  }

}

object Tests {
  import Test._

  def main(args: Array[String]):Unit = {
    mustFail(classOf[Parser#ParserError])(parse("1==1"))
    mustFail(classOf[Checker#Error])(check("1:int"))
    mustFail(classOf[Checker#Error])(check("i:[int]=[1,2,3,4]"))
    mustFail(classOf[Checker#Error])(check("append : [int] -> [int] -> [int] = l -> m  = l + m"))
    mustFail(classOf[Checker#Error])(check("y= 3 \n x = 1+\"a\""))
    mustFail(classOf[Parser#ParserError])(parse("2==2"))
    mustFail(classOf[Checker#Error])(check("x = \"praveen\""))
    mustFail(classOf[Parser#ParserError])(parse("theory EnumeratedType {" +
      "type univ " +
      "enum: [univ] " +
      "complete: |- forall x: univ. x in enum" +
      "} " +
      "theory IntBasedType { " +
      "include EnumeratedType" +
      " type univ = int" +
      "}"))
    mustFail(classOf[Parser#ParserError])(parse("y = true"))
    mustFail(classOf[Checker#Error])(check("x : [int] = [1]"))
    mustFail(classOf[Parser#ParserError])(parse("1+2 == 3"))
    mustFail(classOf[Parser#ParserError])(parse("theory A{ type univ = int } \n x = A { univ = 1}"))
    mustFail(classOf[Parser#ParserError])(parse("x = [1,7]"))
  }
}
