theory Tuples {
  pair: (int, int) = (2, 3)
  result: int
}

inst = Tuples {result = pair(1) + pair(2)}
