import Mathlib.Tactic
set_option maxHeartbeats 0
set_option Elab.async false

/-! Exact degree-twelve Bernstein subdivision in one variable. The operations
use integer coefficients and multiply the represented polynomial by 4096 at
one half-split. This file proves the algebra used by the trivariate checker. -/
namespace D4Bound.SphericalSign.Bernstein
abbrev I := Fin 13
noncomputable def basis (i : I) (x : ℝ) : ℝ :=
  (Nat.choose 12 i : ℝ) * x^i.val * (1-x)^(12-i.val)
noncomputable def E (p : I → ℝ) (x : ℝ) : ℝ := ∑ i, p i * basis i x

def lcoef (i j : I) : ℤ := if j.val ≤ i.val then (Nat.choose i.val j.val : ℤ)*2^(12-i.val) else 0
def rcoef (i j : I) : ℤ := if i.val ≤ j.val then (Nat.choose (12-i.val) (j.val-i.val) : ℤ)*2^i.val else 0

theorem basis_nonneg (i : I) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ basis i x := by
  unfold basis
  positivity

theorem sum_basis (x : ℝ) : (∑ i : I, basis i x) = 1 := by
  norm_num [basis,Fin.sum_univ_succ,Nat.choose]
  ring

theorem E_mono {p q : I → ℝ} {x : ℝ} (hp : ∀ i, p i ≤ q i)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : E p x ≤ E q x := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hp i) (basis_nonneg i hx hx1)

theorem E_const (c x : ℝ) : E (fun _ => c) x = c := by
  rw [E,← Finset.mul_sum,sum_basis,mul_one]

theorem E_bound {p : I → ℝ} {x L : ℝ} (hp : ∀ i, p i ≤ L)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : E p x ≤ L := by
  simpa only [E_const] using E_mono hp hx hx1

theorem left_basis (j : I) (x : ℝ) :
    (∑ i : I, (lcoef i j : ℝ)*basis i x) = 4096*basis j (x/2) := by
  fin_cases j <;> norm_num [lcoef,basis,Fin.sum_univ_succ,Nat.choose] <;> ring

theorem right_basis (j : I) (x : ℝ) :
    (∑ i : I, (rcoef i j : ℝ)*basis i x) = 4096*basis j ((x+1)/2) := by
  fin_cases j <;> norm_num [rcoef,basis,Fin.sum_univ_succ,Nat.choose] <;> ring

theorem E_left (p : I → ℝ) (x : ℝ) :
    E (fun i => ∑ j : I, (lcoef i j : ℝ)*p j) x = 4096*E p (x/2) := by
  simp only [E,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, mul_comm (p _) (basis _ x),← mul_assoc,← Finset.sum_mul,left_basis]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem E_right (p : I → ℝ) (x : ℝ) :
    E (fun i => ∑ j : I, (rcoef i j : ℝ)*p j) x = 4096*E p ((x+1)/2) := by
  simp only [E,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, mul_comm (p _) (basis _ x),← mul_assoc,← Finset.sum_mul,right_basis]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end D4Bound.SphericalSign.Bernstein
