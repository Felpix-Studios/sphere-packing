import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (4,5,6). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck456 : fullCheckG capUse (1/2^0) caseFuel 4 5 6 = true := by
  native_decide

end D4Bound.V7
