import D4Bound.V7CyclicNativeUnits

/-! Native check of the full cyclic case (2,5,5). -/
namespace D4Bound.V7
open CyclicNative

theorem fullCheck255 : fullCheckG capUse (caseUnitG 2 5 5) caseFuel 2 5 5 = true := by
  native_decide

end D4Bound.V7
