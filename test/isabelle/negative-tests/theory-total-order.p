module Test103 {




theory partial_order {
  le: a -> a -> bool
  refl: |- forall x. le(x,x)
  anti_sym: |- forall x,y. le(x,y) & le(y,x) => x == y
  trans: |- forall x,y,z. le(x,y) & le(y,z) => le(x,z)
}

theory total_order {
    include partial_order
    total: |- forall x,y. le(x,y) | le(y,x)


}