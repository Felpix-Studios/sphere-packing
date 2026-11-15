import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (3,6,6). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck366 : fullCheckG capUse (caseUnitG 3 6 6) caseFuel 3 6 6 = true := by
  native_decide

end D4Bound.V7
