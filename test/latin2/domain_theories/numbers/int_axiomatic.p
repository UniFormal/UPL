module int_axiomatic {
  theory IntUnary {
      include .nat_axiomatic.NatUnary
  }

  theory IntPlus {
      include IntUnary
      include .nat_axiomatic.NatPlus
  }

  theory IntPlusTimes {
      include IntUnary
      include .nat_axiomatic.NatPlusTimes
  }

  theory IntSub {
      include IntPlusTimes
  }

  theory Int {
      include .nat_axiomatic.Nat
      include IntSub
  }
}
