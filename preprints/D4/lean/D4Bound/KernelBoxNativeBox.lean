import D4Bound.KernelBoxNativeNode
import D4Bound.KernelBoxNativeScalar

/-!
# From executable checks to `KernelBox V7.kernel`

`kernelBox_of_checks` turns `scalarCheck = true` and `checkAll lam j fuel = true` into the
geometric statement `KernelBox V7.kernel (cellHi (j-1)) lam`. It uses only the standard
axioms. The Boolean facts are established by `native_decide` in the separate modules
`KernelBoxNativeCheckScalar`, `KernelBoxNativeCheck1` and `KernelBoxNativeCheck5`.
-/

namespace D4Bound.KBN
open V7
open scoped RealInnerProductSpace

def checkAll (lam : ℚ) (j fuel : ℕ) : Bool :=
  (List.range j).all fun kr => (List.range j).all fun ks =>
    checkCell (baseP ghat lam kr ks) kr ks fuel

theorem kernelBox_of_checks {lam : ℚ} {j fuel : ℕ} (hj : 0 < j) (hj5 : j ≤ 5)
    (hs : scalarCheck = true) (hc : checkAll lam j fuel = true) :
    KernelBox V7.kernel (cellHi (j - 1)) lam := by
  have hg := scalar_upper_of_check hs
  intro y z hy1 hyR hz1 hzR hin
  have hR : (cellHi (j - 1) : ℝ) ≤ 102597 / 100000 := by
    interval_cases j <;> simp [cellHi, breaks] <;> norm_num
  obtain ⟨kr, hkr, hr⟩ := exists_cell hj hy1 hyR
  obtain ⟨ks, hks, hs'⟩ := exists_cell hj hz1 hzR
  have hcell := List.all_eq_true.mp (List.all_eq_true.mp hc kr (List.mem_range.mpr hkr)) ks
    (List.mem_range.mpr hks)
  have hcc := hcell
  simp only [checkCell, Bool.and_eq_true, decide_eq_true_eq] at hcc
  obtain ⟨⟨⟨⟨⟨⟨okr, oks⟩, cr⟩, cs⟩, kr5⟩, ks5⟩, _⟩ := hcc
  have hB : BaseOK (baseP ghat lam kr ks) lam kr ks := fun r s t h =>
    baseP_le hg lam h kr5 ks5 cr cs t
  have hy0 : 0 < ‖y‖ := by linarith
  have hz0 : 0 < ‖z‖ := by linarith
  have hyz : 0 < ‖y‖ * ‖z‖ := mul_pos hy0 hz0
  have ht2 : ⟪y, z⟫ / (‖y‖ * ‖z‖) ≤ -(133 / 250) := by
    rw [div_le_iff₀ hyz]; linarith
  have ht1 : -1 ≤ ⟪y, z⟫ / (‖y‖ * ‖z‖) := by
    rw [le_div_iff₀ hyz]
    have := abs_real_inner_le_norm y z
    rw [abs_le] at this; linarith
  have hy00 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy1; linarith
  have hz00 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz1; linarith
  have hk : V7.kernel y z = pair ‖y‖ ‖z‖ (⟪y, z⟫ / (‖y‖ * ‖z‖)) := by
    have hy74 : ¬ (7 / 4 < ‖y‖) := by linarith
    have hz74 : ¬ (7 / 4 < ‖z‖) := by linarith
    unfold V7.kernel
    rw [if_neg (not_or.mpr ⟨hy74, hz74⟩), if_neg hy00, if_neg hz00, if_pos ⟨hy1, hz1⟩]
  have := checkCell_sound hB hcell hr hs' ht1 ht2
  unfold Target at this
  rw [hk]
  linarith

theorem kernel_box_1_of_checks (hs : scalarCheck = true)
    (hc : checkAll (3 / 1000000) 1 60 = true) : KernelBox V7.kernel R1 (3 / 1000000) := by
  have h := kernelBox_of_checks (by norm_num) (by norm_num) hs hc
  have e1 : ((cellHi (1 - 1) : ℚ) : ℝ) = R1 := by
    simp [cellHi, breaks, R1]
  have e2 : (((3 / 1000000 : ℚ)) : ℝ) = 3 / 1000000 := by norm_num
  rw [e1, e2] at h
  exact h

theorem kernel_box_5_of_checks (hs : scalarCheck = true)
    (hc : checkAll (1 / 1000000) 5 60 = true) : KernelBox V7.kernel R5 (1 / 1000000) := by
  have h := kernelBox_of_checks (by norm_num) (by norm_num) hs hc
  have e1 : ((cellHi (5 - 1) : ℚ) : ℝ) = R5 := by
    simp [cellHi, breaks, R5]
  have e2 : (((1 / 1000000 : ℚ)) : ℝ) = 1 / 1000000 := by norm_num
  rw [e1, e2] at h
  exact h

end D4Bound.KBN
