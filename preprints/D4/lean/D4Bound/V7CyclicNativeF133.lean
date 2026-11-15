import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (1,3,3). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck133 : fullCheckG capUse (caseUnitG 1 3 3) caseFuel 1 3 3 = true := by
  native_decide

end D4Bound.V7
