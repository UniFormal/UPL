module Queue{
    length = (l : [int]) -> {
      var m : int = 0
      for (_ in l){
        m = 1 + m
      }
      m
    }
  test = {
    length([1,2,3,4,5]) == 5
  }
}