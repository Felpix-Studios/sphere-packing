import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (0,5,6). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck056 : fullCheckG capUse (1/2^0) caseFuel 0 5 6 = true := by
  native_decide

end D4Bound.V7
