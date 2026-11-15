import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (6,6,6). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck666 : fullCheckG capUse (2^18) caseFuel 6 6 6 = true := by
  native_decide

end D4Bound.V7
