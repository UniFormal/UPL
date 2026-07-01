matchExistingFailure = () -> {
  var expected = 1
  if ((expected, val x) = (2, 3)) x else 4
}