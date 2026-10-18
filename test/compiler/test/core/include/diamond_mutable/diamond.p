theory Base {
  mutable count: int = 1
  initialize = {count = count + 1}
}

theory Left {
  include Base
}

theory Right {
  include Base
}

theory Diamond {
  include Left
  include Right
}
