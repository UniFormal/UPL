theory Test020
  imports Complex_Main
begin

definition o1 :: "int option" where
  "o1 = Some 0"
definition o2 :: "int option" where
  "o2 = Some 1"
definition o3 :: "int option" where
  "o3 = None"

end