import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (2,5,6). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck256 : fullCheckG capUse (caseUnitG 2 5 6) caseFuel 2 5 6 = true := by
  native_decide

end D4Bound.V7
