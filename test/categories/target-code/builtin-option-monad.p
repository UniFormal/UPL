module BuiltinOptMonad {

    // UPL monad implementation:
    // there are builtin monad types: list, set, tuple, option
    // they can be called with the return, bind, fmap methods and used within the do notation
    // there is aoo a mechanism for user-defined monads

    // values of type option can be called with the monad methods fmap, return, bind
    o1: option[int] = [1]
    o2: option[int] = []

    mo1 = fmap(o1, (x:int) -> x+1))
    mo2 = fmap(o2, (x:int) -> x+1))
    ret: option[int] = return(1)
    inttochar: int -> option[string] = n -> n match {
            1 -> ["a"]
            2 -> ["b"]
            3 -> ["c"]
            4 -> ["d"]
        }
    bo1 = bind(o1, inttochar)
    bmo1 = bind(mo1, inttochar)
    bo2 = bind(o2, inttochar)

    // 1. monad law: return(x).bind(f) = f x
    o1l: option[string] = return(1).bind(inttochar)
    o1r: option[string] = inttochar(1)

    // 2. monad law: mx.bind(return) == mx
    o2r = o1
    o2l = bind(o2r, return)

    // 3. monad law: mx.bind(f).bind(g) = mx.bind(x -> (f(x)).bind(g))
    chartoint: string -> option[int] = n -> n match {
            "a" -> [1]
            "b" -> [2]
            "c" -> [3]
            "d" -> [4]
        }
    o3l = o1.bind(inttochar).bind(chartoint)
    o3r = o1.bind(x -> inttochar(x).bind(chartoint))


    testopt = {
        o1 == [1] & o2 == [] &
        mo1 == [2] & mo2 == [] &
        ret == [1] &
        bo1 == ["a"] & bmo1 == ["b"] & bo2 == [] &
        // 1. monad law
        o1l == o1r &
        o1r == ["a"]
        // 2. monad law
        o2l == o2r
        // 3. monad law
        o3l == o3r &
        o3r == o1
    }

}