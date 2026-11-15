import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (5,5,5). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck555 : fullCheckG capUse (2^6) caseFuel 5 5 5 = true := by
  native_decide

end D4Bound.V7
