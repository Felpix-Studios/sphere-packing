import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (1,1,4). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck114 : fullCheckG capUse (caseUnitG 1 1 4) caseFuel 1 1 4 = true := by
  native_decide

end D4Bound.V7
