module numbers {
  theory Numbers {
  }

  theory Plus {
      include Numbers
  }

  theory Times {
      include Numbers
  }

  theory PlusTimes {
      include Plus
      include Times
  }
}
