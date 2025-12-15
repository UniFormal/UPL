module OptionMonad {

    theory OptionMonad {
        type X
        type Y

        return: X -> option[X] = (x: X) -> [x]

        bind: option[X] -> (X -> option[Y]) -> option[Y]
        bind = (ox: option[X]) -> (f: X -> option[Y]) -> {
            ox match {
                [] -> []
                [x] -> f(x)
            }
        }
    }

    intOptionMonad = OptionMonad {
        type X = int
        type Y = int
    }

    // list, set (generalize to collections?), tuple is not (why?),

    o1 = intOptionMonad.return(1)
    o2 = intOptionMonad.bind(option[1])(x -> option[x+1])

    test = {
        o1 == option[1] &
        o2 == option[2]
    }
}