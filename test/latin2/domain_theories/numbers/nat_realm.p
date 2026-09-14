module nat_realm {
  NatToBinary: .nat_binary.Binary -> .nat_axiomatic.NatAx = n -> §{
      include .numbers.Numbers
      include .numbers.Plus
      include .numbers.Times
  }

  BinaryToNat: .nat_axiomatic.NatAx -> .nat_binary.Binary = b -> §{
      include .numbers.Numbers
      include .numbers.Plus
      include .numbers.Times
  }
}
