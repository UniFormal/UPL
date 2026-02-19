theory Test082
  imports Complex_Main
begin

definition a :: "complex" where
  "a = (2 ^ 3)"
definition b :: "real" where
  "b = (2.0999999046325684 ^ 3)"
definition c :: "real" where
  "c = (2 powr 3.0999999046325684)"
definition d :: "real" where
  "d = (2.0999999046325684 powr 3.0999999046325684)"

end