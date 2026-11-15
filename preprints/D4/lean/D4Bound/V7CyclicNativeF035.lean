import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (0,3,5). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck035 : fullCheckG capUse (caseUnitG 0 3 5) caseFuel 0 3 5 = true := by
  native_decide

end D4Bound.V7
