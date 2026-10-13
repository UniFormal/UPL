module rat_axiomatic {
  theory RatDiv {
      include .int_axiomatic.IntSub
  }

  theory Rat {
      include .int_axiomatic.Int
      include RatDiv
  }
}
