import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (2,2,4). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck224 : fullCheckG capUse (caseUnitG 2 2 4) caseFuel 2 2 4 = true := by
  native_decide

end D4Bound.V7
