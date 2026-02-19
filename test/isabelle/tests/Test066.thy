theory Test066
  imports Main
begin

definition comp :: "('B => 'C) => ('A => 'B) => ('A => 'C)" where
  "comp = (\<lambda>g f. (\<lambda>x. (g (f x))))"

end