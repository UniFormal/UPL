swap : ((int, int)) -> (int, int) = (p: (int, int)) -> (p(2), p(1))
pick : (bool, int) -> ((int, bool), int) = (b: bool, n: int) -> if (b) ((n, true), 1) else ((0, false), 2)
second : (((int, bool), int)) -> int = (p: ((int, bool), int)) -> p match {
    ((a, b), c) -> if (b) a + c else c
}
tupleValues = () -> {
    val s = swap((3, 40))
    val t = pick(true, s(1))
    val u = pick(false, 7)
    s(1) + second(t) + second(u) + t(1)(1)
}
