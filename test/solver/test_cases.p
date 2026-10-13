module SolverTestCases {
  theory Base {
    x : float
    y : float
    z : float
    // x O y == z
  }
  theory BaseX {
    include Base
    y = 2.0
    z = 3.0
  }
  theory BaseY {
    include Base
    x = 1.0
    z = 3.0
  }
  theory BaseZ {
    include Base
    x = 1.0
    y = 2.0
  }
  
  // ADD

  theory AddBaseL {
    include Base
    a :|- x+y == z
  }
  theory AddBaseR {
    include Base
    a :|- z == x+y
  }
  theory AddXL {
    include BaseX
    include AddBaseL
  }
  theory AddXR {
    include BaseX
    include AddBaseR
  }
  theory AddYL {
    include BaseY
    include AddBaseL
  }
  theory AddYR {
    include BaseY
    include AddBaseR
  }
  theory AddZL {
    include BaseZ
    include AddBaseR
  }
  theory AddZR {
    include BaseZ
    include AddBaseL
  }

  theory Solutions {
    include Base

    AddXL:|- x == z-y
    AddXR:|- z-y == x
    AddYL:|- y == z-x
    AddYR:|- z-x==y
    AddZL:|- z == x+y
    AddZR:|- x+y == z
  }
  
  ///////////////////////////////// SUB
  ///////////////////////////////// MULT
  ///////////////////////////////// DIV
  ///////////////////////////////// EXP
  ///////////////////////////////// UNARY MINUS
}