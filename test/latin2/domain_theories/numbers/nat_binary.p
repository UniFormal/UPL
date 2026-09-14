module nat_binary {
  theory NumBinary {
      include .numbers.Numbers
  }

  theory BinaryPlus {
      include NumBinary
      include .numbers.Plus
  }

  theory BinaryPlusTimes {
      include BinaryPlus
      include .numbers.Times
  }

  theory Binary {
      include BinaryPlusTimes
  }
}
