import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (0,0,2). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck002 : fullCheckG capUse (caseUnitG 0 0 2) caseFuel 0 0 2 = true := by
  native_decide

end D4Bound.V7
