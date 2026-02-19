theory Basics007
  imports Main
begin

definition v1 :: "'new_name" where
"v1 = undefined"
definition v3 :: "'new_name => unit" where
  "v3 = (\<lambda>x. ())"

end