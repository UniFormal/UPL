theory Test015
  imports Main
begin

definition x :: int where
  "x = 0"
definition y :: int where
  "y = (if (x = 0) then 1 else 0)"

end