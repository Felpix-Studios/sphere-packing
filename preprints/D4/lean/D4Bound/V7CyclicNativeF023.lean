import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (0,2,3). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck023 : fullCheckG capUse (caseUnitG 0 2 3) caseFuel 0 2 3 = true := by
  native_decide

end D4Bound.V7
