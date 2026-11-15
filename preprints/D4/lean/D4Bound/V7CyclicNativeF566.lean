import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (5,6,6). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck566 : fullCheckG capUse (2^14) caseFuel 5 6 6 = true := by
  native_decide

end D4Bound.V7
