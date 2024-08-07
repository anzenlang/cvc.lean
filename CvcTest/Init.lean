namespace Cvc.Test

variable [Repr α] [BEq α]

/-- Crashes with an explanation if `expected ≠ value`. -/
def check! (expected value : α) : IO Unit :=
  if expected != value then do
    println! "expected `{repr expected}`, got `{repr value}`"
    panic! "check failed"
  else return ()

/-- Crashes with an explanation if `expected ≠ value`. -/
def checkNe! (lhs rhs : α) : IO Unit :=
  if lhs == rhs then do
    println! "`{repr lhs}` should be different from `{repr rhs}`, but is not"
    panic! "check failed"
  else return ()

end Test
