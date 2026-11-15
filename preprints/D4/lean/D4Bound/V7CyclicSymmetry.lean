import D4Bound.V7CyclicGeometry

/-! Symmetry of the actual fixed V7 pair and canonical triangle cases. -/
namespace D4Bound.V7
noncomputable section

lemma gramPair_swap (r s t : ℝ) : gramPair r s t = gramPair s r t := by
  simp only [gramPair,mul_comm,mul_left_comm,mul_assoc]
lemma capsCorrection_swap (r s t : ℝ) : capsCorrection r s t = capsCorrection s r t := by
  simp only [capsCorrection,add_comm]
lemma tentsCorrection_swap (r s t : ℝ) : tentsCorrection r s t = tentsCorrection s r t := by
  simp only [tentsCorrection,add_comm]
lemma allocationsCorrection_swap (r s t : ℝ) :
    allocationsCorrection r s t = allocationsCorrection s r t := by
  have h : r*r+s*s+2*r*s*t = s*s+r*r+2*s*r*t := by ring
  simp only [allocationsCorrection,h,add_comm]
lemma conditionalPair_swap (r s : ℝ) : conditionalPair r s = conditionalPair s r := by
  simp only [conditionalPair,mul_comm,mul_left_comm,mul_assoc,add_comm]
lemma sphericalPair_swap (r s t : ℝ) : sphericalPair r s t = sphericalPair s r t := by
  simp only [sphericalPair,mul_comm,mul_left_comm,mul_assoc]
lemma graphRadial_swap (g : Graph) (hg : g ∈ graphs) (r s : ℝ) :
    graphRadial g r s ↔ graphRadial g s r := by
  norm_num [graphs] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [graphRadial,and_comm,or_comm]
lemma graphsCorrection_swap (r s t : ℝ) : graphsCorrection r s t = graphsCorrection s r t := by
  unfold graphsCorrection
  apply congrArg List.sum
  apply List.map_congr_left
  intro g hg
  rw [graphRadial_swap g hg r s]

/-- Symmetry of all three concrete rational count matrices is checked by exact arithmetic. -/
lemma countPair_sum_swap (r s : ℝ) :
    (countPolynomials.map fun c => countPair c r s).sum =
      (countPolynomials.map fun c => countPair c s r).sum := by
  norm_num [countPolynomials,countPair,List.range_succ,List.sum_cons,List.sum_nil]
  ring

theorem pair_swap (r s t : ℝ) : pair r s t = pair s r t := by
  unfold pair rawPair
  rw [gramPair_swap r s t,sphericalPair_swap r s t,conditionalPair_swap r s,
    countPair_sum_swap r s,capsCorrection_swap r s t,tentsCorrection_swap r s t,
    allocationsCorrection_swap r s t,graphsCorrection_swap r s t]
  ring

lemma sideCos_swap (r s d : ℝ) : sideCos r s d = sideCos s r d := by
  unfold sideCos
  congr 1 <;> ring

lemma sideCyclic_swap12 (r s d : ℝ) : sideCyclic r s d = sideCyclic s r d := by
  unfold sideCyclic
  rw [sideCos_swap r s d,pair_swap r s]
  ring

lemma sideCyclic_swap23 (r s d : ℝ) : sideCyclic r s d = sideCyclic r d s := by
  unfold sideCyclic
  rw [sideCos_swap s d r,pair_swap s d]
  ring

/-- It suffices to certify the canonical ordered full and exterior cases. -/
theorem cyclicSign_of_ordered_side_certificates
    (full : ∀ r s d : ℝ, 1 ≤ r → r ≤ s → s ≤ d → d ≤ 7/4 → sideCyclic r s d ≤ 0)
    (outside : ∀ r s d : ℝ, 1 ≤ r → r ≤ s → s ≤ 7/4 →
      7/4 < d → d ≤ r+s → pair r s (sideCos r s d) ≤ 0) : CyclicSign kernel := by
  apply cyclicSign_of_side_certificates
  · intro r s d hr hR hs hS hd hD
    rcases le_total r s with hrs | hsr
    · rcases le_total s d with hsd | hds
      · exact full r s d hr hrs hsd hD
      · rcases le_total r d with hrd | hdr
        · rw [sideCyclic_swap23]; exact full r d s hr hrd hds hS
        · rw [sideCyclic_swap23,sideCyclic_swap12]; exact full d r s hd hdr hrs hS
    · rcases le_total r d with hrd | hdr
      · rw [sideCyclic_swap12]; exact full s r d hs hsr hrd hD
      · rcases le_total s d with hsd | hds
        · rw [sideCyclic_swap12,sideCyclic_swap23]; exact full s d r hs hsd hdr hR
        · rw [sideCyclic_swap23,sideCyclic_swap12,sideCyclic_swap23]
          exact full d s r hd hds hsr hR
  · intro r s d hr hR hs hS hd htri
    rcases le_total r s with hrs | hsr
    · exact outside r s d hr hrs hS hd htri
    · rw [sideCos_swap,pair_swap]
      exact outside s r d hs hsr hR hd (by simpa [add_comm] using htri)

#print axioms pair_swap
#print axioms cyclicSign_of_ordered_side_certificates
end
end D4Bound.V7
