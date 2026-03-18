module Basics008 {

  // Arithmetic operators:

  int_add(x,y:: int): int = x+y
  rat_add(x,y:: rat): rat = x+y
  float_add(x,y::float):float = x+y
  // Type inference guesses that all arguments have the same type. Mixed-type arguments are converted as needed.
  float_add2(x:float, y) = x+y // (float,float)->float
  int_float_add(x: int, y: float) = x+y // (int,float)->float

  // Accordingly for -, *, /, <=, >=, <, >.

  // Division by 0 throws a run-time exception.
  int_div(x,y:: int) = x/y // (int,int) -> rat


}