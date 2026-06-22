factorial: int -> int
factorial = x -> {
  if (x<=0) 1 else x * factorial(x-1)
}