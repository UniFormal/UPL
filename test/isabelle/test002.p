module Test002 {

    // comment

    f: int -> int = x -> x

    g: int -> int -> int = x -> y -> x + y

    h: int -> int -> bool -> bool = x -> y -> z -> z

    i(x: int, y: int) = x + y

    // is a problem, needs context, see test200
    // g: int -> int
    // g(x) = x
}