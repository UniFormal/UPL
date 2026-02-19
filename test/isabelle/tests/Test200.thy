theory Test200
  imports Main
begin

definition g :: "int => int" where
  "g = (\<lambda>x. x)"
definition y :: "int" where
  "y = g 1"

end