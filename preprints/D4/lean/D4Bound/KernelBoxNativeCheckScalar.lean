import D4Bound.KernelBoxNativeScalar

/-! `native_decide` component: the scalar gauge bound `ghat` (see `KernelBoxNativeScalar`). -/

namespace D4Bound.KBN

theorem scalarCheck_true : scalarCheck = true := by native_decide

end D4Bound.KBN
