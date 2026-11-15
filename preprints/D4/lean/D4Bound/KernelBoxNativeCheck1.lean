import D4Bound.KernelBoxNativeBox
import D4Bound.KernelBoxNativeCheckScalar

/-! `native_decide` component: the `R1` kernel box (one cell pair, `λ = 3/10⁶`). -/

namespace D4Bound.KBN

theorem check1_true : checkAll (3 / 1000000) 1 60 = true := by native_decide

/-- Premise `kernel_box_1` of `d4_density_bound_concrete`. -/
theorem kernel_box_1_native : KernelBox V7.kernel R1 (3 / 1000000) :=
  kernel_box_1_of_checks scalarCheck_true check1_true

end D4Bound.KBN

#print axioms D4Bound.KBN.kernel_box_1_native
#print axioms D4Bound.KBN.kernel_box_1_of_checks
