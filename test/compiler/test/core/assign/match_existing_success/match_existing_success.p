matchExistingSuccess = () -> {
  var expected = 2
  if ((expected, val x) = (2, 3)) x else 0
}