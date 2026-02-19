theory Basics009
  imports Main
begin

definition returns_true :: "bool" where
  "returns_true = ((\<lambda>x. x) = (\<lambda>x. x))"
definition would_fail :: "bool" where
  "would_fail = (\<lambda>. ((\<lambda>x. (x + 1)) = (\<lambda>x. x)))"

end