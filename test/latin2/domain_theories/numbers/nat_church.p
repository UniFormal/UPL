module nat_church {
  // Church numerals use a trick to define natural numbers as certain functions relative to an
  // arbitrary empty fixed type
  theory ChurchNaturals {
      include .sfol.SFOLEQND
  }

  theory ChurchNaturalsPlus {
      include ChurchNaturals
  }

  theory ChurchNaturalsPlusTimes {
      include ChurchNaturalsPlus
  }
}
