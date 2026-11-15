import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (2,6,6). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck266 : fullCheckG capUse (caseUnitG 2 6 6) caseFuel 2 6 6 = true := by
  native_decide

end D4Bound.V7
