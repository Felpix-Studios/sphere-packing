import D4Bound.V7CyclicOutsideExtWS
import D4Bound.V7CyclicOutsideParams

/-! Native check of sub-box LH of the exterior cyclic case (5,5). Written by hand by
p-31a0ecd56021 (cyclicoutside); see cyclicoutside-native/notes.md. -/
namespace D4Bound.V7

theorem xs55LH : extCheckWS xoCapUse (1/2^8 : ℚ) xoFuel 5 5 (102597/100000) (5/4) (5/4) (3/2) = true := by
  native_decide

end D4Bound.V7
