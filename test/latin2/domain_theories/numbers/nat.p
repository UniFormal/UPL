module nat {
  theory Nat {
  }

  theory NatPlus {
      include Nat
  }

  theory NatPlusTimes {
      include NatPlus
  }

  theory Int {
      include NatPlusTimes
  }
}
