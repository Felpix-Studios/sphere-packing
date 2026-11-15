import D4Bound.V7CensusGramBasic
import D4Bound.V7CensusGramBernstein

namespace D4Bound.V7.CensusGram
open Finset
noncomputable section
open Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pieceValue (v : List ℚ) (p : ℕ) (r : ℝ) : ℝ :=
  ((List.range 7).map fun i => (v.getD (7*p+i) 0 : ℝ)*basisValue p i r).sum

theorem radialValue_eq_pieceValue (v : List ℚ) (r : ℝ) :
    radialValue v r = pieceValue v (radialPiece r) r := rfl

theorem list_sum_swap {α β : Type*} (L : List α) (J : List β) (f : α → β → ℝ) :
    (L.map fun a => (J.map fun b => f a b).sum).sum =
      (J.map fun b => (L.map fun a => f a b).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, List.sum_map_add]

theorem radialValue_combination {α : Type*} (L : List α) (w : α → ℚ)
    (v : α → List ℚ) (q : List ℚ)
    (he : ∀ k, k < 49 → (L.map fun a => w a*(v a).getD k 0).sum = q.getD k 0)
    {r : ℝ} (hr : r ≤ 7/4) :
    (L.map fun a => (w a : ℝ)*radialValue (v a) r).sum = radialValue q r := by
  unfold radialValue
  simp_rw [← List.sum_map_mul_left]
  rw [list_sum_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hilt : i < 7 := List.mem_range.mp hi
  have hk : 7*radialPiece r+i < 49 := by have := radialPiece_lt_seven hr; omega
  simp_rw [← mul_assoc, List.sum_map_mul_right]
  congr 1
  have hc : (L.map fun a => (w a : ℝ)*((v a).getD (7*radialPiece r+i) 0 : ℝ)).sum =
      ((L.map fun a => w a*(v a).getD (7*radialPiece r+i) 0).sum : ℚ) := by
    clear he
    induction L with
    | nil => simp
    | cons a L ih => simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, ih]
  rw [hc, he _ hk]

/-- A radial lower bound summed over the neighbourhood gives its exact cumulative-count floor. -/
theorem radial_count_floor (v a : List ℚ) (X : Finset E4)
    (h : ∀ x ∈ X, ((List.range 5).map fun j =>
      (a.getD j 0 : ℝ)*indicator (breaks.getD (j+1) 0) ‖x‖).sum ≤ radialValue v ‖x‖) :
    ((List.range 5).map fun j => (a.getD j 0 : ℝ)*
      (countWithin X ((breaks.getD (j+1) 0 : ℚ) : ℝ) : ℝ)).sum ≤
      ∑ x ∈ X, radialValue v ‖x‖ := by
  have hh := Finset.sum_le_sum h
  rw [sum_list_map] at hh
  simp_rw [← Finset.mul_sum, indicator_sum] at hh
  exact hh
end
end D4Bound.V7.CensusGram
