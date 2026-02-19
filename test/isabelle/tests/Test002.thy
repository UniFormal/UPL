theory Test002
  imports Main
begin

definition f :: "int => int" where
  "f = (\<lambda>x. x)"
definition g :: "int => (int => int)" where
  "g = (\<lambda>x. (\<lambda>y. (x + y)))"
definition h :: "int => (int => (bool => bool))" where
  "h = (\<lambda>x. (\<lambda>y. (\<lambda>z. z)))"
definition i :: "int => int => int" where
  "i = (\<lambda>y x. (x + y))"

end