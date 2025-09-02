module Monoid {

    theory Monoid {
        // monoid as set st with operation op (st,op) associative and a unit neutral element
        // binary operation and neutral element
        type T
        //st: set[T]
        id: T
        op: T -> T -> T


        neutRight: |- forall a. op(a)(id) == a
        neutLeft: |- forall b. op(id)(b) == b
        assoc: |- forall a,b,c. op(op(a)(b))(c) == op(a)(op(b)(c))

    }

    // In the examples we declare and prove the types (sets of values) as monoids (instance of a theory)
    // example: natural numbers, +

    // example: integers, -

    // example: reals, *

    // example: string concatenation


    // a monoid as category is a single object category
    theory Monoid2 {
        C: CatST.CategoryST
        // C must only have a single object
        single_obj: |- forall a, b: C.object. a == b
    }


    // future: somehow prove equivalence between monoid theories?
}