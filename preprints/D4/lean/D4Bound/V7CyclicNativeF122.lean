import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (1,2,2). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck122 : fullCheckG capUse (caseUnitG 1 2 2) caseFuel 1 2 2 = true := by
  native_decide

end D4Bound.V7
