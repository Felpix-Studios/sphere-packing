import D4Bound.V7CountEnergy
import D4Bound.CensusCheck
import D4Bound.V7Radial
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Algebra used by the concrete count projection and supporting-plane witnesses.
The hypotheses of these generic identities are exact equations checked separately. -/
namespace D4Bound.V7.CensusGram
open Finset Matrix
noncomputable section

/-- An exact projection lower bound from a positive-semidefinite quadratic form.
The two range identities avoid any nonsingularity assumption on the large Gram matrix. -/
theorem projection_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι ι ℝ) (A : Matrix ι κ ℝ)
    (x b : ι → ℝ) (n c : κ → ℝ)
    (hM : M.IsSymm) (hpos : ∀ z : ι → ℝ, 0 ≤ z ⬝ᵥ (M *ᵥ z))
    (hMb : M *ᵥ b = A *ᵥ c)
    (hAx : Aᵀ *ᵥ x = n) (hAb : Aᵀ *ᵥ b = n) :
    n ⬝ᵥ c ≤ x ⬝ᵥ (M *ᵥ x) := by
  have hxc : x ⬝ᵥ (M *ᵥ b) = n ⬝ᵥ c := by
    rw [hMb, dotProduct_mulVec, ← mulVec_transpose, hAx]
  have hbc : b ⬝ᵥ (M *ᵥ b) = n ⬝ᵥ c := by
    rw [hMb, dotProduct_mulVec, ← mulVec_transpose, hAb]
  have hsym : b ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (M *ᵥ b) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm]
  have h := hpos (x-b)
  simp only [mulVec_sub, sub_dotProduct, dotProduct_sub, hsym, hxc, hbc] at h
  linarith

/-- Every rational ray-centre gives an affine supporting plane for a sum of squares. -/
theorem ray_center_bound {ι : Type*} (S : Finset ι) (w u z a : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    (∑ i ∈ S, w i*(2*a i*u i-a i^2)) +
      ∑ i ∈ S, 2*w i*a i*z i ≤ ∑ i ∈ S, w i*(u i+z i)^2 := by
  have h : 0 ≤ ∑ i ∈ S, w i*(u i+z i-a i)^2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have he : (∑ i ∈ S, w i*(u i+z i)^2) -
      ((∑ i ∈ S, w i*(2*a i*u i-a i^2)) + ∑ i ∈ S, 2*w i*a i*z i) =
      ∑ i ∈ S, w i*(u i+z i-a i)^2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- The seven degree-six Bernstein features sum to one on every basis piece. -/
theorem basisValue_sum (p : ℕ) (r : ℝ) :
    ((List.range 7).map fun i => basisValue p i r).sum = 1 := by
  norm_num [basisValue, List.range_succ, Nat.choose]
  ring

end
end D4Bound.V7.CensusGram
