import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (0,2,5). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck025 : fullCheckG capUse (caseUnitG 0 2 5) caseFuel 0 2 5 = true := by
  native_decide

end D4Bound.V7
