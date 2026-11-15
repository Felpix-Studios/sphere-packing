import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (2,4,5). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck245 : fullCheckG capUse (caseUnitG 2 4 5) caseFuel 2 4 5 = true := by
  native_decide

end D4Bound.V7
