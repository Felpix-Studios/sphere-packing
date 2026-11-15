import D4Bound.CyclicNativeExtSound
import D4Bound.CyclicNativeAllocLo

/-! Soundness of `allocProfLo2`. Standard axioms only. -/
namespace D4Bound.CyclicNative
open V7

lemma allocProfLo2_sound (c : AllocationData) {qh : ℚ} {x : ℝ} (hx : x ≤ qh) :
    ((allocProfLo2 (toAllocN c) qh : ℚ) : ℝ) ≤ allocationProfile c x := by
  have base := allocProfLo_sound c hx
  unfold allocProfLo2
  by_cases ht : (toAllocN c).twoLevel = true
  · rw [if_pos ht]; exact base
  · rw [if_neg ht]
    by_cases h4 : (1:ℚ)/4 ≤ qh
    · rw [if_pos h4]; exact base
    · rw [if_neg h4]
      dsimp only
      by_cases hs : 0 ≤ sqrtUp qh ∧ sqrtUp qh ≤ 1 ∧ qh ≤ sqrtUp qh ^ 2
      · rw [if_pos hs]
        obtain ⟨hs0, hs1, hsq⟩ := hs
        have ht' : c.twoLevel = false := by simpa [toAllocN] using ht
        have hq4 : x < 1/4 := by
          have h4' : qh < 1/4 := lt_of_not_ge h4
          have : ((qh : ℚ) : ℝ) < ((1/4 : ℚ) : ℝ) := by exact_mod_cast h4'
          push_cast at this
          linarith
        -- the classical profile on q < 1/4
        have hprof : allocationProfile c x = min 1 (2*(1-Real.sqrt x)^2) := by
          unfold allocationProfile
          rw [if_neg (by simp [ht']), if_neg (by linarith), if_neg (by linarith)]
        have hhalf : ((allocProfLo (toAllocN c) qh : ℚ) : ℝ) = 1/2 := by
          have n2 : ¬ ((1:ℚ)/2 ≤ qh) := fun h => h4 (le_trans (by norm_num) h)
          have e : allocProfLo (toAllocN c) qh = 1/2 := by
            unfold allocProfLo; simp only [toAllocN, ht', Bool.false_eq_true, if_false]
            rw [if_neg n2, if_neg h4]
          rw [e]; norm_num
        rw [hhalf] at base
        push_cast
        apply max_le base
        rw [hprof]
        apply min_le_min le_rfl
        have hs0' : (0:ℝ) ≤ sqrtUp qh := by exact_mod_cast hs0
        have hs1' : (sqrtUp qh : ℝ) ≤ 1 := by exact_mod_cast hs1
        have hsx : Real.sqrt x ≤ (sqrtUp qh : ℝ) := by
          rcases le_or_gt x 0 with hneg | hpos
          · rw [Real.sqrt_eq_zero'.mpr hneg]; exact hs0'
          · exact sqrtUp_ok hpos.le hx hs0 hsq
        have h1 : 0 ≤ 1 - (sqrtUp qh : ℝ) := by linarith
        have h2 : 1 - (sqrtUp qh : ℝ) ≤ 1 - Real.sqrt x := by linarith
        nlinarith [mul_le_mul h2 h2 h1 (le_trans h1 h2)]
      · rw [if_neg hs]; exact base

end D4Bound.CyclicNative

#print axioms D4Bound.CyclicNative.allocProfLo2_sound
