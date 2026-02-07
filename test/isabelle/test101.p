module Test101 {


theory Partial_order {

    type a
    le: (a, a) -> bool

    refl: |- forall x. le(x,x)
    antisym: |- forall x,y. le(x,y) & le(y,x) => (x == y)
    trans: |- forall x,y,z. le(x,y) & le(y,z) => le(x,z)

}


}