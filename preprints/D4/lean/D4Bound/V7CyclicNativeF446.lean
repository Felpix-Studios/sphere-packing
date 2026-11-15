import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (4,4,6). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck446 : fullCheckG capUse (1/2^10) caseFuel 4 4 6 = true := by
  native_decide

end D4Bound.V7
