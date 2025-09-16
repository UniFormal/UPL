module BuiltinSetMonad {

    // UPL monad implementation:
    // there are builtin monad types: list, set, tuple, option
    // they can be called with the return, bind, fmap methods and used within the do notation
    // there is also a mechanism for user-defined monads

    // values of type set can be called with the monad methods fmap, return, bind
    s: set[int] = [1,2,3,4]
    ms: set[int] = s.fmap((x:int) -> x+1))
    ret: set[int] = return(1)
    inttochar: int -> set[string] = n -> n match {
            1 -> ["a"]
            2 -> ["b"]
            3 -> ["c"]
            4 -> ["d"]
        }
    bs: set[string] = s.bind(inttochar)

    // using bind to map from a list to a set monad?
    ls: list[int] = [1,2,3,4]
    bs2: set[int] = s.bind(inttochar)


    // 1. monad law: return(x).bind(f) = f x
    s1l: set[string] = return(1).bind(inttochar)
    s1r: set[string] = inttochar(1)

    // 2. monad law: mx.bind(return) == mx
    s2 = s.bind(return)

    // 3. monad law: mx.bind(f).bind(g) = mx.bind(x -> (f(x)).bind(g))
    chartoint: string -> set[int] = n -> n match {
            "a" -> [1]
            "b" -> [2]
            "c" -> [3]
            "d" -> [4]
        }
    s3l = s.bind(inttochar).bind(chartoint)
    s3r = s.bind(x -> inttochar(x).bind(chartoint))


    testlist = {
        ms == set[2,3,4,5] &
        ret == set[1] &
        bs == set["a","b","c","d"] &
        // 1. monad law
        s1l == s1r &
        s1r == set["a"]
        // 2. monad law
        ms == s &
        // 3. monad law
        s3l == s3r &
        s3r == s
    }

}