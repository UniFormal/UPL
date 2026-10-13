module Test {
    fun : (int -> int) -> int = (f: (int -> int)) -> f(2)

    test = fun(x -> x + 4)
}