import D4Bound.ComponentsCapacity
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Strictly negative pairwise inner products force affine independence.
This supplies the finite-dimensional count needed by the narrow graph and
the strict ball-count branch. No spherical count theorem is assumed. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.Components
noncomputable section
open Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem affineIndependent_of_inner_neg {ι : Type*} (v : ι → V)
    (hneg : ∀ i j, i ≠ j → ⟪v i,v j⟫ < 0) : AffineIndependent ℝ v := by
  apply affineIndependent_iff.mpr
  intro s w hw hvec
  by_contra hn
  have hp : ∃ i ∈ s, 0 < w i := by
    by_contra h
    push Not at h
    exact hn ((Finset.sum_eq_zero_iff_of_nonpos h).mp hw)
  have hm : ∃ j ∈ s, w j < 0 := by
    by_contra h
    push Not at h
    exact hn ((Finset.sum_eq_zero_iff_of_nonneg h).mp hw)
  obtain ⟨i0, hi0, hpi0⟩ := hp
  obtain ⟨j0, hj0, hmj0⟩ := hm
  let p := fun i => max (w i) 0
  let m := fun i => max (-w i) 0
  have hp0 : ∀ i, 0 ≤ p i := fun i => le_max_right _ _
  have hm0 : ∀ i, 0 ≤ m i := fun i => le_max_right _ _
  have he : ∀ i, w i = p i-m i := by
    intro i
    by_cases hi : 0 ≤ w i
    · simp only [p, m, max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), sub_zero]
    · have hi' : w i ≤ 0 := le_of_not_ge hi
      simp only [p, m, max_eq_right hi', max_eq_left (neg_nonneg.mpr hi')]
      ring
  have hsum : (∑ i ∈ s, p i • v i) = ∑ i ∈ s, m i • v i := by
    simp_rw [he, sub_smul] at hvec
    rw [Finset.sum_sub_distrib] at hvec
    exact sub_eq_zero.mp hvec
  have hterm : ∀ i ∈ s, ∀ j ∈ s, p i*m j*⟪v i,v j⟫ ≤ 0 := by
    intro i hi j hj
    by_cases hpi : 0 < w i
    · by_cases hmj : w j < 0
      · have hij : i ≠ j := by intro hij; subst j; linarith
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hp0 i) (hm0 j))
          (hneg i j hij).le
      · have hz : m j = 0 := max_eq_right (by linarith)
        rw [hz]; simp
    · have hz : p i = 0 := max_eq_right (le_of_not_gt hpi)
      rw [hz]; simp
  have hstrict : p i0*m j0*⟪v i0,v j0⟫ < 0 := by
    have hij : i0 ≠ j0 := by intro hij; subst j0; linarith
    have hp' : 0 < p i0 := lt_of_lt_of_le hpi0 (le_max_left _ _)
    have hm' : 0 < m j0 := lt_of_lt_of_le (neg_pos.mpr hmj0) (le_max_left _ _)
    exact mul_neg_of_pos_of_neg (mul_pos hp' hm') (hneg i0 j0 hij)
  have hinner : ⟪∑ i ∈ s, p i • v i, ∑ j ∈ s, m j • v j⟫ =
      ∑ i ∈ s, ∑ j ∈ s, p i*m j*⟪v i,v j⟫ := by
    rw [sum_inner]
    simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hstrictsum : (∑ i ∈ s, ∑ j ∈ s, p i*m j*⟪v i,v j⟫) < 0 := by
    apply Finset.sum_neg'
    · intro i hi
      exact Finset.sum_nonpos (hterm i hi)
    · refine ⟨i0, hi0, ?_⟩
      exact Finset.sum_neg' (hterm i0 hi0) ⟨j0, hj0, hstrict⟩
  rw [← hinner, hsum] at hstrictsum
  exact (not_lt_of_ge real_inner_self_nonneg) hstrictsum

theorem card_le_finrank_succ_of_inner_neg [FiniteDimensional ℝ V]
    (X : Finset V) (hneg : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ⟪x,y⟫ < 0) :
    X.card ≤ Module.finrank ℝ V + 1 := by
  have ha := affineIndependent_of_inner_neg (fun x : X => (x : V))
    (fun x y hxy => hneg x x.property y y.property (by
      intro he
      exact hxy (Subtype.ext he)))
  have hc := ha.card_le_finrank_succ
  have hd := Submodule.finrank_le (vectorSpan ℝ (Set.range fun x : X => (x : V)))
  simpa only [Fintype.card_coe] using hc.trans (Nat.add_le_add_right hd 1)

end
end D4Bound.Components
