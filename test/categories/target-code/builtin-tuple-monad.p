module BuiltinTupleMonad {

    // UPL monad implementation:
    // there are builtin monad types: list, set, tuple, option
    // they can be called with the return, bind, fmap methods and used within the do notation
    // there is also a mechanism for user-defined monads

    // questions about tuples:
    // 1. mutable vs immutable types
    // 2. appending tuples isn't as trivial as appending lists: appending to a tuple changes its type

    // values of type tuple can be called with the monad methods fmap, return, bind
    t: (int,string) = (1,"foo")

    // defining fmap isn't, because the passed function would need to be polymorphic in type int and string
    // mt: some_tuple_type = t.fmap(some_anon_fun)

    // unary tuples also make a problem
    ret: (int,) = return(1)

    // no unary tuples for mapping
    //inttochar: int -> tuple[string] = n -> n match {
    //        1 -> ["a"]
    //        2 -> ["b"]
    //        3 -> ["c"]
    //        4 -> ["d"]
    //    }
    // bs: tuples[string] = ls.bind(inttochar)

    test = {
        true
    }

}