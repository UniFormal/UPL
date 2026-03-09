module Basics012 {


  // Collections form a subtype hierarchy using both inclusion and quotient.
  // In particular, options and lists are special cases of sets:
  quotient_list_to_set:  set[int] = list[1,1,2]
  include_option_to_set: set[int] = option[0]


}