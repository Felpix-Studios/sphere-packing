import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (1,5,6). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck156 : fullCheckG capUse (caseUnitG 1 5 6) caseFuel 1 5 6 = true := by
  native_decide

end D4Bound.V7
