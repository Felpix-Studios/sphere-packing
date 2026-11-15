import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (0,4,4). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck044 : fullCheckG capUse (caseUnitG 0 4 4) caseFuel 0 4 4 = true := by
  native_decide

end D4Bound.V7
