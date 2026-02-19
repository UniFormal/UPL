theory Test021
  imports Complex_Main
begin

definition l1 :: "int list" where
  "l1 = [1,2,3,4]"
definition l2 :: "int list" where
  "l2 = (0 # l1)"

end