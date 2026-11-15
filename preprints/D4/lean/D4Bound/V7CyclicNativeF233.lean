import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (2,3,3). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck233 : fullCheckG capUse (caseUnitG 2 3 3) caseFuel 2 3 3 = true := by
  native_decide

end D4Bound.V7
