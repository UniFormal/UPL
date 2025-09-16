module BuiltinListMonad {

    // UPL monad implementation:
    // there are builtin monad types: list, set, tuple, option
    // they can be called with the return, bind, fmap methods and used within the do notation
    // there is also a mechanism for user-defined monads

    // values of type list can be called with the monad methods fmap, return, bind
    ls: [int] = [1,2,3,4]
    mls: [int] = ls.fmap((x:int) -> x+1))
    ret: [int] = return(1) // [].return(1)
    inttochar: int -> [string] = n -> n match {
            1 -> ["a"]
            2 -> ["b"]
            3 -> ["c"]
            4 -> ["d"]
        }
    bls: list[string] = ls.bind(inttochar)

    // 1. monad law: return(x).bind(f) = f x
    ls1l: [string] = return(1).bind(inttochar)
    ls1r: [string] = inttochar(1)

    // 2. monad law: mx.bind(return) == mx
    ls2 = ls.bind(return)

    // 3. monad law: mx.bind(f).bind(g) = mx.bind(x -> (f(x)).bind(g))
    chartoint: string -> [int] = n -> n match {
            "a" -> [1]
            "b" -> [2]
            "c" -> [3]
            "d" -> [4]
        }
    ls3l = ls.bind(inttochar).bind(chartoint)
    ls3r = ls.bind(x -> inttochar(x).bind(chartoint))


    testlist = {
        mls == [2,3,4,5] &
        ret == [1] &
        bls == ["a","b","c","d"] &
        // 1. monad law
        ls1l == ls1r &
        ls1r == ["a"]
        // 2. monad law
        mls == ls &
        // 3. monad law
        ls3l == ls3r &
        ls3r == ls
    }

}