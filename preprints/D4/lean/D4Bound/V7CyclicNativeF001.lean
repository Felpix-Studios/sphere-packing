import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (0,0,1). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck001 : fullCheckG capUse (caseUnitG 0 0 1) caseFuel 0 0 1 = true := by
  native_decide

end D4Bound.V7
