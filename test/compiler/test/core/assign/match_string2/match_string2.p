matchString = () -> {
  var expected = "abc"
  Uniformal.print(if ((expected, val y) = ("abc", "matched")) y else "not_matched")
}