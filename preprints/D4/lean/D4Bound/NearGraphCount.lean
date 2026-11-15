import D4Bound.AnnularCert

/-! The exact degree-six Delsarte polynomial for the near antipodal graph.
Its factorization certifies the full closed interval, including both endpoints.
Coefficients are those in NEAR_ANTIPODAL_EXTERIOR_GRAPH_THEOREM.md.
-/
open Finset
namespace D4Bound.NearGraphCertificate
noncomputable section

def coefficients : Fin 6 → ℝ :=
  ![43173/339488, 24391/169744, 5625/42436, 30609/339488, 15609/339488, 1/64]

def rest (t : ℝ) : ℝ := ∑ i : Fin 6,
  coefficients i * (Polynomial.Chebyshev.U ℝ ((i.val+1 : ℕ) : ℤ)).eval t

theorem polynomial_identity (t : ℝ) :
    46955/678976 + rest t = (t-5609/10609)*(t+1)*(t+1/2)^2*t^2 := by
  norm_num [rest, coefficients, Fin.sum_univ_succ]
  rw [AnnularCertificate.U2, AnnularCertificate.U3,
    AnnularCertificate.U4, AnnularCertificate.U5, AnnularCertificate.U6]
  ring

theorem rest_energy : SphereEnergyNonneg rest := by
  have hc : ∀ i : Fin 6, 0 ≤ coefficients i := by
    intro i
    fin_cases i <;> norm_num [coefficients]
  exact sphereEnergy_sum Finset.univ coefficients (fun i : Fin 6 => i.val+1)
    (fun i _ => hc i)

theorem code_thirty : SphericalCodeBound (5609/10609) 30 := by
  apply sphericalCodeBound_of_energy (5609/10609) (46955/678976) (22500/10609)
    30 rest (by norm_num) (by norm_num) rest_energy
  · rw [polynomial_identity]
    norm_num
  · intro t ht ht'
    rw [polynomial_identity]
    apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg t)
    apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg (t+1/2))
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

end
end D4Bound.NearGraphCertificate
