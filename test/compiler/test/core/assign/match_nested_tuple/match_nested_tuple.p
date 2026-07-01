matchNestedTuple = () -> {
  if (((val a, val b), val c) = ((1, 2), 3)) a+b+c else 0
}