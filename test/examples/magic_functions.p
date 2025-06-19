module Magic {
  theory A {
    x: int
    // magic infix operator: a ++ n becomes a._++_(n); here: add n to x
    val _++_ = (y: int) -> A{x=..x+y}
    // magic circumfix operator: 〈a,b,c〉 becomes a.〈_〉(list[b,c]); here: sum a.x + b.x + ...
    val 〈_〉 = (as: list[A]) -> {
      var i = x
      for (u in as) i = i+u.x
      A{x=i}
    }
  }

  a = A{x=1}
  test = (a++2).x == 3 & 〈a,a,a〉.x == 3
}