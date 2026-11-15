import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (1,5,5). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck155 : fullCheckG capUse (caseUnitG 1 5 5) caseFuel 1 5 5 = true := by
  native_decide

end D4Bound.V7
