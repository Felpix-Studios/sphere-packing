import D4Bound.CensusArithmetic

/-! An explicit size check for the same exhaustive census traversal. -/
namespace D4Bound.CensusArithmetic

def vectorCountAt (N : ℕ) : ℕ :=
  ((List.range (min N 25 + 1)).map fun n3 =>
  ((List.range (min n3 24 + 1)).map fun n2 =>
  ((List.range (n2 + 1)).map fun n1 =>
  ((List.range (n1 + 1)).map fun n0 =>
    if (n0 = 24 → N = 24) ∧ (n1 = 24 → n3 = 24)
    then 1 else 0).sum).sum).sum).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem census_traversal_size : ((List.range 27).map vectorCountAt).sum = 165503 := by
  decide +kernel

end D4Bound.CensusArithmetic
