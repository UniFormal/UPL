theory Basics006
  imports Main
begin

definition id :: "int => int" where
  "id = (\<lambda>x. x)"
definition id0 :: "int" where
  "id0 = (id 0)"

end