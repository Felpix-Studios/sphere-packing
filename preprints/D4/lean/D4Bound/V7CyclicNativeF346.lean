import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (3,4,6). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck346 : fullCheckG capUse (1/2^10) caseFuel 3 4 6 = true := by
  native_decide

end D4Bound.V7
