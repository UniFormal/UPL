module ListMonad {

    theory ListMonad {
        type X
        type Y

        return: X -> list[X] = (x: X) -> [x]

        // need append for bind
        append: (list[Y], list[Y]) -> list[Y]
        append = (xs, ys) -> {
            xs match {
                [] -> ys
                x -: xs2 -> x -: append(xs2, ys)
            }
        }

        // lists as nondeterministic computations
        bind: list[X] -> (X -> list[Y]) -> list[Y]
        bind = (lx: list[X]) -> (f: X -> list[Y]) -> {
            lx match {
                [] -> []
                x -: xs -> append(f(x), bind(xs)(f))
            }
        }
    }

    intListMonad = ListMonad {
        type X = int
        type Y = X
    }

    // list, set (generalize to collections?), tuple is not (why?),

    l1 = intListMonad.return(1)
    l2 = intListMonad.bind(list[1,2,3,4])(x -> list[x+1])

    test = {
        l1 == list[1] &
        l2 == [2,3,4,5]
    }
}