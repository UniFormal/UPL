
module Test200 {

    // tests merging of declarations with the same name by checker

    g: int -> int
    g = x -> x

    y = g(1)

}