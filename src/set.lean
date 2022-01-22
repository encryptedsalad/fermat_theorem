namespace BasicFunctions

inductive Weekday where
  | sunday    : Weekday
  | monday    : Weekday
  | tuesday   : Weekday
  | wednesday : Weekday
  | thursday  : Weekday
  | friday    : Weekday
  | saturday  : Weekday

def natOfWeekday (d : Weekday) : Nat :=
  match d with
  | sunday    → 1
  | monday    → 2
  | tuesday   → 3
  | wednesday → 4
  | thursday  → 5
  | friday    → 6
  | saturday  → 7

#eval natOfWeekday monday

