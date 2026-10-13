factorial = (x:int) -> {
  if (x<=0) return 1
  var result = 1
  var i = 1
  while (i<=x) {
    result = result*i
    i = i+1
  }
  result
}

sum = (x:int) -> {
  if (x<=0) return 0
  var result = 0
  var i = 1
  while (i<=x) {
    result = result+i
    i = i+1
  }
  result
}