import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (0,0,0). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck000 : fullCheckG capUse (caseUnitG 0 0 0) caseFuel 0 0 0 = true := by
  native_decide

end D4Bound.V7
