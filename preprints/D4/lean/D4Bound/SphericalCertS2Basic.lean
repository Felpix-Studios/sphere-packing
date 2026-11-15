import D4Bound.SphericalCertLegendre
import D4Bound.Geometry
import Mathlib.Tactic

/-! Sound Delsarte certificate composition for the unit sphere in R3. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound

/-- Nonnegative unweighted energy on every finite unit code. -/
def Sphere2EnergyNonneg (h : ℝ → ℝ) : Prop :=
  ∀ C : Finset (EuclideanSpace ℝ (Fin 3)), (∀ u ∈ C, ‖u‖ = 1) →
    0 ≤ ∑ u ∈ C, ∑ v ∈ C, h ⟪u,v⟫

lemma sphere2Energy_legendre (k : ℕ) :
    Sphere2EnergyNonneg (fun t => Schoenberg2.legendre k t) := by
  intro C hC
  simpa using schoenberg_S2 k C id (fun _ => 1) hC

lemma sphere2Energy_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (k : ι → ℕ)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    Sphere2EnergyNonneg (fun t => ∑ i ∈ s, c i * Schoenberg2.legendre (k i) t) := by
  classical
  intro C hC
  have he : (∑ u ∈ C, ∑ v ∈ C, ∑ i ∈ s,
      c i * Schoenberg2.legendre (k i) ⟪u,v⟫) =
      ∑ i ∈ s, c i * (∑ u ∈ C, ∑ v ∈ C,
        Schoenberg2.legendre (k i) ⟪u,v⟫) := by
    simp_rw [Finset.mul_sum]
    calc
      _ = ∑ u ∈ C, ∑ i ∈ s, ∑ v ∈ C,
          c i * Schoenberg2.legendre (k i) ⟪u,v⟫ := by
        apply Finset.sum_congr rfl
        intro u hu
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [he]
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (sphere2Energy_legendre (k i) C hC)

/-- A real polynomial kernel with positive constant energy and nonpositive off-diagonal
values gives a strict cardinality bound. The constant, signs and PSD terms are checked
separately for each exact certificate. -/
theorem sphericalCodeBound3_of_energy (s A B : ℝ) (m : ℕ) (h : ℝ → ℝ)
    (hA : 0 < A) (hB : B < (m + 1 : ℕ) * A)
    (henergy : Sphere2EnergyNonneg h)
    (hdiag : A + h 1 = B)
    (hsign : ∀ t : ℝ, -1 ≤ t → t ≤ s → A + h t ≤ 0) :
    (∀ C : Finset (EuclideanSpace ℝ (Fin 3)), (∀ u ∈ C, ‖u‖ = 1) →
      (∀ u ∈ C, ∀ v ∈ C, u ≠ v → ⟪u,v⟫ ≤ s) → C.card ≤ m) := by
  classical
  intro C hC hsep
  have hlow : (C.card : ℝ)^2 * A ≤
      ∑ u ∈ C, ∑ v ∈ C, (A + h ⟪u,v⟫) := by
    have he := henergy C hC
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    nlinarith
  have hhigh : (∑ u ∈ C, ∑ v ∈ C, (A + h ⟪u,v⟫)) ≤ (C.card : ℝ) * B := by
    calc
      _ ≤ ∑ u ∈ C, ∑ v ∈ C, if u = v then B else 0 := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        by_cases huv : u = v
        · subst v
          simp only [if_true]
          have hu1 : ⟪u,u⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hC u hu]; norm_num
          rw [hu1, hdiag]
        · rw [if_neg huv]
          apply hsign
          · have hl := (abs_le.mp (abs_real_inner_le_norm u v)).1
            simpa [hC u hu, hC v hv] using hl
          · exact hsep u hu v hv huv
      _ = _ := by simp [Finset.sum_ite_eq', hC]
  by_contra hm
  have hN : (m + 1 : ℕ) ≤ C.card := by omega
  have hNr : ((m + 1 : ℕ) : ℝ) ≤ C.card := by exact_mod_cast hN
  have hpos : (0 : ℝ) < C.card := by exact_mod_cast (by omega : 0 < C.card)
  have hBA : B < (C.card : ℝ) * A := lt_of_lt_of_le hB (mul_le_mul_of_nonneg_right hNr hA.le)
  have hmul := mul_lt_mul_of_pos_left hBA hpos
  nlinarith

end D4Bound
