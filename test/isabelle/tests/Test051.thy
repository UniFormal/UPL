theory Test051
  imports Main
begin

definition v :: "bool" where
  "v = (0 = 1)"
definition w :: "bool" where
  "w = (0 \<noteq> 1)"

end