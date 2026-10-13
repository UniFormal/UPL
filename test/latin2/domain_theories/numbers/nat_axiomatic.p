module nat_axiomatic {
  theory NatUnary {
      include .numbers.Numbers
  }

  theory NatPeano {
      include NatUnary
  }

  theory NatPlus {
      include NatUnary
      include .numbers.Plus
  }

  theory NatPlusTimes {
      include NatPlus
      include .numbers.Times
  }

  theory NatParity {
      include NatUnary
  }

  theory NatAx {
      include NatPeano
      include NatPlusTimes
      include NatParity
  }

  theory NatLiterals {
      include NatUnary
  }

  theory Nat {
      include NatPeano
      include NatPlusTimes
      include NatParity
      include NatLiterals
  }
}
