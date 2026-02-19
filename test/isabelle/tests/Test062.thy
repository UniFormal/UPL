theory Test062
  imports Main
begin

typedecl a
definition f :: "a => a" where
  "f = (\<lambda>x. x)"

end