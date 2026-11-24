g : (int) -> (int, int) = (x: int) -> if (x > 0) x match {
    1 -> (1, 2)
    n -> if (n > 5) (n, 0) else (0, n)
} else (7, 7)
