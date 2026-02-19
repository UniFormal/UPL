module Test311 {

    map@(A,B): _
    // (A -> B) -> list[A] -> list[B] throws illegal type error
    map@(A,B) = f -> l -> {
      l match {
        [] -> list[]
        h -: t -> f(h) -: map(f)(t)  // if type arguments are omitted from an expression symbol, they are treated like @(_,...,_) and are inferred
      }
    }

    }