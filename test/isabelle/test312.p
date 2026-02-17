module Test312 {



    map@(A,B): (A -> B) -> list[A] -> list[B]
    map@(A,B)(f: A -> B, l: list[A]) = {
      l match {
        [] -> list[]
        h -: t -> f(h) -: map(f,t)  // if type arguments are omitted from an expression symbol, they are treated like @(_,...,_) and are inferred
      }
    }

}