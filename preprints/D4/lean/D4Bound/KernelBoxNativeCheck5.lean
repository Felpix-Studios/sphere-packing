import D4Bound.KernelBoxNativeBox
import D4Bound.KernelBoxNativeCheckScalar

/-! `native_decide` component: the `R5` kernel box (25 cell pairs, `λ = 1/10⁶`). -/

namespace D4Bound.KBN

theorem check5_true : checkAll (1 / 1000000) 5 60 = true := by native_decide

/-- Premise `kernel_box_5` of `d4_density_bound_concrete`. -/
theorem kernel_box_5_native : KernelBox V7.kernel R5 (1 / 1000000) :=
  kernel_box_5_of_checks scalarCheck_true check5_true

end D4Bound.KBN

#print axioms D4Bound.KBN.kernel_box_5_native
#print axioms D4Bound.KBN.kernel_box_5_of_checks
