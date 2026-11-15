import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (4,4,5). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck445 : fullCheckG capUse (caseUnitG 4 4 5) caseFuel 4 4 5 = true := by
  native_decide

end D4Bound.V7
