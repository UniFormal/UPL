module Block {

  testNewline = {
    val x = 1
    val f = (u:int) -> u+1
    // postfix operations like (), [], ., etc. must be at the end of the line
    // parsed as function application
    val fx = f(
      x
    )
    // parsed as two expression the second of which happens to be bracketed
    val y = x
    (x+y)*2
  }

}