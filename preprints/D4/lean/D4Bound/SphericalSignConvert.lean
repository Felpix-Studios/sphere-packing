import D4Bound.SphericalSignBernstein
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign.Bernstein

/-- Integer matrix taking degree-at-most-twelve power coefficients to
27720 times their Bernstein coefficients. -/
def powerMatrix (i j : I) : ℤ :=
  if j.val ≤ i.val then (Nat.choose i.val j.val : ℤ)*(27720/(Nat.choose 12 j.val : ℤ)) else 0

lemma power_basis (j : I) (x : ℝ) :
    (∑ i : I, (powerMatrix i j : ℝ)*basis i x) = 27720*x^j.val := by
  fin_cases j <;> norm_num [powerMatrix,basis,Fin.sum_univ_succ,Nat.choose] <;> ring

noncomputable def powerEval (p : I → ℝ) (x : ℝ) : ℝ := ∑ i, p i*x^i.val
lemma E_powerMatrix (p : I → ℝ) (x : ℝ) :
    E (fun i => ∑ j : I, (powerMatrix i j : ℝ)*p j) x = 27720*powerEval p x := by
  simp only [E,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc,mul_comm (p _) (basis _ x),← mul_assoc,← Finset.sum_mul,power_basis]
  rw [powerEval,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms E_powerMatrix
end D4Bound.SphericalSign.Bernstein
