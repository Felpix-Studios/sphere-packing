import D4Bound.V7CountEnergy
import D4Bound.ComponentsGram

/-! The concrete V7 Gegenbauer recurrence and Gram rays. -/
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

theorem chebU_eq (n : ℕ) (t : ℝ) :
    chebU n t = (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval t := by
  induction n using Nat.twoStepInduction with
  | zero => simp [chebU]
  | one => simp [chebU]
  | more n hn hn1 =>
    simp only [chebU, Nat.cast_add, Nat.cast_ofNat, Polynomial.Chebyshev.U_add_two,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      hn, hn1, Nat.cast_one]

theorem zonal_eq (n : ℕ) (t : ℝ) : zonal n t = Components.zfun n t := by
  simp [zonal, Components.zfun, chebU_eq]

theorem zonal_posDef (n : ℕ) (X : Finset E4) (hX : (0 : E4) ∉ X) (c : E4 → ℝ) :
    0 ≤ ∑ x ∈ X, ∑ y ∈ X, c x*c y*zonal n (⟪x,y⟫/(‖x‖*‖y‖)) := by
  simp_rw [zonal_eq]
  exact Components.zfun_posDef n X hX c

end
end D4Bound.V7
