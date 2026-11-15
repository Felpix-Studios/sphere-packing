import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (3,3,3). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck333 : fullCheckG capUse (caseUnitG 3 3 3) caseFuel 3 3 3 = true := by
  native_decide

end D4Bound.V7
