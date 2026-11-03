theory ClosureLambda {
  x = 5
  fun : int -> int = (y: int) -> x + y

  test = fun(4)
}