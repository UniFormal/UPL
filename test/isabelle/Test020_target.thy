theory Test020_target
  imports Main
begin

definition o1 :: "int option" where
  "o1 = Some 0"

definition o2 where
  "o2 = Some (1 :: int)"

definition o3 :: "int option" where
  "o3 = None"

end