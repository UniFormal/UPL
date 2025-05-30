module simpleMonads{
    // Playing around with creating some simple Monads I would like to have,
    // Maybe and Either to be exact 

    // Conclusion: 
    // 1. Without type Parameters, there is little point in them
    // 2. There is no way to get functions inside of them
    // 3. There is no way to get values out of them

    theory Maybe{
        type maybe
        nothing: maybe
        just: int -> maybe
    }

    noFunctor: _ = (f:int -> int) -> Maybe{f(1)}

    mapMaybe: _ 
    = (f: _) -> (m: _) -> m match{
        Maybe.nothing -> Maybe.nothing
        Maybe{just(`value`)} -> _ //Maybe{just(f(`value`))}
    }

    showMaybe:  _
    = (m: _) -> m match{
        Maybe.nothing -> 0
        Maybe{just(`value`)} -> value
    }

map: (int -> int) -> [int] -> [int] 
map = (f: int -> int) -> l -> l match{
    [] -> []
    x -: xs -> f(x) -: map(f)(xs)
}

none:_ = []
one:_ = [1]

succ:_ = (x:int) -> x+1

two: _ = map (x -> x+1)(one)
stillNone: _ = map(succ)(none)

    theory Maybe2{
        type a 
        theory MaybeA{
            type maybeA
            nothing: maybeA
            just: a -> maybeA
        }
        // map: _ -> _ -> _
        // = (f: _) -> (m: _) -> m match{
        //     MaybeA.nothing -> MaybeA.nothing
        //     MaybeA{just(`a`)} -> MaybeA{just(f(`a`))}
        // }
    }

    type maybeRat = Maybe2{a = rat}.MaybeA
    savediv: rat -> rat -> maybeRat
    = (x:rat) -> (y:rat) -> {
        if (y == 0) maybeRat.nothing
    }
}