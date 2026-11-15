import D4Bound.CertificateInterval
import Mathlib.Analysis.Calculus.Taylor

/-! The second-order lower-bound step used by a centered interval certificate. -/
namespace D4Bound.CertificateInterval

open Set

/-- A scalar second-order Taylor lower bound on the parameter interval [0,1].
Applying this to `u ↦ F(c + u*d)` turns a Hessian bound into a boxwise lower bound. -/
theorem taylor_lower_01 {f : ℝ → ℝ} {g L : ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hg : HasDerivAt f g 0)
    (hL : ∀ t ∈ Ioo (0 : ℝ) 1, L ≤ iteratedDeriv 2 f t) :
    f 0 + g + L/2 ≤ f 1 := by
  have hU : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hV : uIoo (0 : ℝ) 1 = Ioo 0 1 := uIoo_of_le zero_le_one
  have hf' : ContDiffOn ℝ ((1+1 : ℕ)) f (uIcc (0 : ℝ) 1) := by simpa [hU] using hf
  obtain ⟨t, ht, hT⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x₀ := (0 : ℝ)) (x := (1 : ℝ)) (n := 1) (by norm_num) hf'
  have hu : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 0 :=
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) 0 (by norm_num)
  have hd : derivWithin f (Icc (0 : ℝ) 1) 0 = g := hg.hasDerivWithinAt.derivWithin hu
  have hp : taylorWithinEval f 1 (uIcc (0 : ℝ) 1) 0 1 = f 0 + g := by
    simp [taylorWithinEval_succ, iteratedDerivWithin_one, hd]
  rw [hp] at hT
  have hLt := hL t (by simpa [hV] using ht)
  norm_num at hT
  linarith

/-- A proved lower surrogate and certified center, slope and curvature bounds suffice. -/
theorem lower_surrogate_nonnegative {F f : ℝ → ℝ} {g c₀ g₀ H₀ : ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc 0 1)) (hg : HasDerivAt f g 0)
    (hF : f 1 ≤ F 1) (hc : c₀ ≤ f 0) (hg₀ : g₀ ≤ g)
    (hH : ∀ t ∈ Ioo (0 : ℝ) 1, H₀ ≤ iteratedDeriv 2 f t)
    (hcheck : 0 ≤ c₀ + g₀ + H₀/2) : 0 ≤ F 1 := by
  have h := taylor_lower_01 hf hg hH
  linarith

end D4Bound.CertificateInterval
