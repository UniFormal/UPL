module Test300 {

    // test functions
    // Current approach: Compile to Isabelle definitions with lambda expressions, because every UPL function is a lambda expression.

    f: int -> int = x -> x

    g: int -> int -> int = x -> y -> x + y

    h: int -> int -> bool -> bool = x -> y -> z -> z

    i(x: int, y: int) = x + y

    //g: int -> int
    //g(x) = x
}