import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (3,5,6). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck356 : fullCheckG capUse (1/2^0) caseFuel 3 5 6 = true := by
  native_decide

end D4Bound.V7
