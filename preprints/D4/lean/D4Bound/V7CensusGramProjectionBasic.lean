import Mathlib.Tactic
namespace D4Bound.V7.CensusGram
open Finset
noncomputable section
open Classical
set_option maxHeartbeats 0
set_option Elab.async false

theorem list_finset_sum_swap {α β : Type*} (L : List α) (S : Finset β)
    (f : α → β → ℝ) :
    (L.map fun i => ∑ j ∈ S, f i j).sum = ∑ j ∈ S, (L.map fun i => f i j).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp [ih, Finset.sum_add_distrib]

theorem list_square_expand {α : Type*} (L : List α) (w y b : α → ℝ) :
    (L.map fun i => w i*(y i-b i)^2).sum =
      (L.map fun i => w i*(y i)^2).sum -
      2*(L.map fun i => w i*y i*b i).sum +
      (L.map fun i => w i*(b i)^2).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [ih]
    ring

theorem weighted_projection_bound {α β : Type*} [Fintype β]
    (L : List α) (w y : α → ℝ) (d : α → β → ℝ)
    (G : β → β → ℝ) (n : β → ℝ)
    (hw : ∀ i ∈ L, 0 ≤ w i)
    (hc : ∀ j, (L.map fun i => w i*y i*d i j).sum = ∑ k, G j k*n k)
    (hg : ∀ j k, (L.map fun i => w i*d i j*d i k).sum = G j k) :
    (∑ j, ∑ k, n j*G j k*n k) ≤ (L.map fun i => w i*(y i)^2).sum := by
  let b : α → ℝ := fun i => ∑ j, d i j*n j
  have hcross : (L.map fun i => w i*y i*b i).sum = ∑ j, ∑ k, n j*G j k*n k := by
    simp only [b, Finset.mul_sum]
    rw [list_finset_sum_swap]
    simp_rw [← mul_assoc, List.sum_map_mul_right, hc, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hsquare : (L.map fun i => w i*(b i)^2).sum = ∑ j, ∑ k, n j*G j k*n k := by
    have he (i : α) : w i*(b i)^2 = ∑ j, ∑ k, (w i*d i j*d i k)*n j*n k := by
      simp only [b, pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    simp_rw [he,list_finset_sum_swap,List.sum_map_mul_right,hg]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hp : 0 ≤ (L.map fun i => w i*(y i-b i)^2).sum := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  have he : (L.map fun i => w i*(y i-b i)^2).sum =
      (L.map fun i => w i*(y i)^2).sum -
      2*(L.map fun i => w i*y i*b i).sum +
      (L.map fun i => w i*(b i)^2).sum := by
    exact list_square_expand L w y b
  rw [he,hcross,hsquare] at hp
  linarith
end
end D4Bound.V7.CensusGram
