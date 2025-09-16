

module Pyths {

    theory Pythags {
        // theory about pythagorean numbers would define what they are
        // the set of pythagorean numbers and subsets of it are sets of triples that satisfy x^2+y^2=z^2
        pythags: set[(int,int,int)]
        pyth_ax: |- forall triple in pythags. (triple(1)*triple(1) + triple(2)*triple(2)) == (triple(3)*triple(3))
    }

    // method to compute all pythagorean numbers up to a n
    def pythags(n : Int) : List[(Int,Int,Int)] =
      // Assume ranges produce lists, and `guard` filters inside list comprehensions
      // list is also a monoid with `mappend`
      // but actually we are using sets of bounded ints
      do {  z: set[int[0;n*n]] <- range(1, n)
            y: set[int[0;n*n]] <- range(1, z)
            x: set[int[0;n*n]] <- range(1, y)
            //guard(x*x + y*y == z*z)
            //return (x, y, z)
            if (x*x + y*y == z*z) then return (x, y, z) else return emptyset
      }

    // concrete theory of pythagorean numbers up to 10
    pythags10 = Pythags {pythags = pythags(10), pyth_ax = ???}

}



