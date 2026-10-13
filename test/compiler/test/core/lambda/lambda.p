module Lambda {
  test : (int, int, bool) -> int = (f: int, g: int, b: bool) -> if (b) f * g else f + g
}