module Magic {
  theory A {
    x: int
    // magic infix operator: a ++ n becomes a._infix_++(n); here: add n to x
    val _infix_++ = (y: int) -> A{x=..x+y}
    // magic circumfix operator: 〈a,b,c〉 becomes a._circumfix_〈_〉(list[b,c]); here: sum a.x + b.x + ...
    val _circumfix_〈_〉 = (as: list[A]) -> {
      var i = x
      for (u in as) i = i+u.x
      A{x=i}
    }
  }

  a = A{x=1}
  test = (a++2).x == 3 & 〈a,a,a〉.x == 3
}

module Collections {
   theory Magma {
     type univ
     op: (univ,univ) -> univ # infix ∘
   }
   ishom(M,N:: Magma, f:M -> N) = forall x,y. f(x∘y)==f(x)∘f(y)
}