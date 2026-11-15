import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (4,5,5). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck455 : fullCheckG capUse (1/2^4) caseFuel 4 5 5 = true := by
  native_decide

end D4Bound.V7
