import D4Bound.Density
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Fourier transform of `e^{-2‖x‖²} F(2‖x‖²)` on `ℝ⁴`

For a real polynomial `F(u) = ∑_{k ≤ d} c_k u^k` let `f(x) = e^{-2‖x‖²} F(2‖x‖²)` on
`E4 = EuclideanSpace ℝ (Fin 4)`. With Mathlib's convention `𝓕 g ξ = ∫ e^{-2πi⟨x,ξ⟩} g x dx`
and `s = π²‖ξ‖²/2`, this file proves (`D4Bound.fourier_polyGauss`)

  `𝓕 f ξ = (π²/4) e^{-s} G(s)`,   `G(s) = ∑_k c_k ∑_{j ≤ k} lagR k j s^j`,

where `lagR k j = (-1)^j C(k,j) (k+1)!/(j+1)! = (-1)^j k!/j! C(k+1, k-j)` (`D4Bound.lagR_eq`).
`D4Bound.lagG_eq_coeff` gives `G` in coefficient form, `G_j = ∑_{k ≥ j} c_k lagR k j`.
It also proves continuity and integrability of `f`, integrability of `𝓕 f`,
`Re 𝓕 f ≥ 0` wherever `G ≥ 0` on `[0, ∞)`, and `∫ f = (π²/4) G(0)`.

Proof. Put `J_k(a) = 𝓕(‖x‖^{2k} e^{-a‖x‖²}) ξ` for `a > 0`. Mathlib gives
`J_0(a) = (π/a)² e^{-c/a}`, `c = π²‖ξ‖²` (`fourier_gaussian_innerProductSpace`).
Differentiation under the integral (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) gives
`J_k' = -J_{k+1}`. The closed forms `C_k(a) = π² a^{-(k+2)} e^{-c/a} Q_k(c/a)`, with
`Q_0 = 1`, `Q_{k+1} = (k + 2 - X) Q_k + X Q_k'`, satisfy the same relation, so `J_k = C_k` on
`(0, ∞)` by induction and uniqueness of derivatives. At `a = 2` this is the monomial case;
linearity gives the polynomial case. The coefficients of `Q_k` are `lagR k j` by induction
(`FourierAux.coeff_Q`), using `(k+2) C(k+1,j+1) = (k+3+j) C(k,j+1) + (j+2) C(k,j)`.
-/

open Polynomial

namespace D4Bound.FourierAux

/-- The polynomials `Q_k`, `Q_0 = 1`, `Q_{k+1} = (k + 2 - X) Q_k + X Q_k'`. -/
noncomputable def Q : ℕ → ℝ[X]
  | 0 => 1
  | k + 1 => (C ((k : ℝ) + 2) - X) * Q k + X * derivative (Q k)

/-- Closed form of the coefficients: `(-1)^j C(k,j) (k+1)!/(j+1)!`. -/
noncomputable def lag (k j : ℕ) : ℝ :=
  (-1) ^ j * (k.choose j : ℝ) * ((k + 1).factorial / (j + 1).factorial : ℝ)

lemma choose_id (k j : ℕ) :
    (k + 2) * (k + 1).choose (j + 1) = (k + 3 + j) * k.choose (j + 1) + (j + 2) * k.choose j := by
  rw [Nat.choose_succ_succ]
  have h := Nat.choose_succ_right_eq k j
  rcases le_or_gt j k with hjk | hjk
  · zify [hjk] at h ⊢
    linear_combination (-1 : ℤ) * h
  · simp [Nat.choose_eq_zero_of_lt hjk, Nat.choose_eq_zero_of_lt (by omega : k < j + 1)]

lemma lag_succ_zero (k : ℕ) : lag (k + 1) 0 = ((k : ℝ) + 2) * lag k 0 := by
  simp only [lag, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, zero_add,
    Nat.factorial_one, Nat.factorial_succ (k + 1)]
  push_cast
  ring

lemma lag_succ_succ (k j : ℕ) :
    lag (k + 1) (j + 1) = ((k : ℝ) + 3 + j) * lag k (j + 1) - lag k j := by
  have hc : ((k : ℝ) + 2) * ((k + 1).choose (j + 1) : ℝ) =
      ((k : ℝ) + 3 + j) * (k.choose (j + 1) : ℝ) + ((j : ℝ) + 2) * (k.choose j : ℝ) := by
    exact_mod_cast choose_id k j
  simp only [lag, Nat.factorial_succ (k + 1), Nat.factorial_succ (j + 1)]
  have hD : ((j + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hj : ((j : ℝ) + 1 + 1) ≠ 0 := by positivity
  set F : ℝ := ((k + 1).factorial : ℝ)
  set D : ℝ := ((j + 1).factorial : ℝ)
  set E : ℝ := F / (((j : ℝ) + 1 + 1) * D) with hE
  have e1 : (((k + 1 + 1 : ℕ) : ℝ) * F) / (((j + 1 + 1 : ℕ) : ℝ) * D) = ((k : ℝ) + 2) * E := by
    rw [hE]; push_cast; ring
  have e2 : F / (((j + 1 + 1 : ℕ) : ℝ) * D) = E := by rw [hE]; push_cast; ring
  have e3 : F / D = ((j : ℝ) + 2) * E := by rw [hE]; field_simp; ring
  rw [Nat.cast_mul, Nat.cast_mul, e1, e2, e3, pow_succ]
  linear_combination (-(-1 : ℝ) ^ j * E) * hc

lemma coeff_Q (k j : ℕ) : (Q k).coeff j = lag k j := by
  induction k generalizing j with
  | zero =>
    rcases j with _ | j
    · simp [Q, lag]
    · simp [Q, lag, Polynomial.coeff_one]
  | succ k ih =>
    rcases j with _ | j
    · simp only [Q, sub_mul, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_zero, ih,
        lag_succ_zero]
      ring
    · simp only [Q, sub_mul, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative,
        ih, lag_succ_succ]
      ring

lemma eval_Q (k : ℕ) (w : ℝ) : (Q k).eval w = ∑ j ∈ Finset.range (k + 1), lag k j * w ^ j := by
  have hdeg : (Q k).natDegree < k + 1 := by
    refine Nat.lt_succ_of_le ((natDegree_le_iff_coeff_eq_zero).2 fun N hN => ?_)
    rw [coeff_Q, lag, Nat.choose_eq_zero_of_lt hN]
    simp
  rw [eval_eq_sum_range' hdeg]
  simp only [coeff_Q]

lemma eval_Q_succ (k : ℕ) (w : ℝ) :
    (Q (k + 1)).eval w = ((k : ℝ) + 2 - w) * (Q k).eval w + w * (derivative (Q k)).eval w := by
  simp [Q]

/-- Closed form of the transform at parameter `a`: `π² a^{-(k+2)} e^{-c/a} Q_k(c/a)`. -/
noncomputable def Cf (c : ℝ) (k : ℕ) (a : ℝ) : ℝ :=
  Real.pi ^ 2 * (a⁻¹) ^ (k + 2) * Real.exp (-(c * a⁻¹)) * (Q k).eval (c * a⁻¹)

lemma hasDerivAt_Cf (c : ℝ) (k : ℕ) {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt (Cf c k) (-(Cf c (k + 1) a)) a := by
  have hu : HasDerivAt (fun a : ℝ => a⁻¹) (-(a⁻¹ ^ 2)) a := by
    simpa [inv_pow] using hasDerivAt_inv ha
  have h1 := hu.pow (k + 2)
  have h2 := ((hu.const_mul c).neg).exp
  have h3 := (Polynomial.hasDerivAt (Q k) (c * a⁻¹)).comp a (hu.const_mul c)
  have h := ((h1.const_mul (Real.pi ^ 2)).mul h2).mul h3
  refine h.congr_deriv ?_
  have hk : k + 2 - 1 = k + 1 := by omega
  simp only [Cf, eval_Q_succ, Pi.pow_apply, Pi.neg_apply, Pi.mul_apply, Function.comp_apply, hk,
    Nat.cast_add, Nat.cast_ofNat]
  ring


/-! ### The parametric Gaussian integrals -/

open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace

lemma integrable_gauss {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : E4 => Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E4) (b := (b : ℂ))
    (by simpa using hb) 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [inner_zero_left, ofReal_zero, mul_zero, add_zero]
  rw [Complex.norm_exp]
  congr 1
  simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  norm_cast

lemma pow_gauss_le (m : ℕ) {b : ℝ} (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) :
    t ^ m * Real.exp (-b * t) ≤ (m.factorial * (2 / b) ^ m) * Real.exp (-(b / 2) * t) := by
  have h := Real.pow_div_factorial_le_exp (x := b / 2 * t) (by positivity) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hf] at h
  have h2 : t ^ m ≤ m.factorial * (2 / b) ^ m * Real.exp (b / 2 * t) := by
    have e : t ^ m = (b / 2 * t) ^ m * (2 / b) ^ m := by
      rw [← mul_pow]; congr 1; field_simp
    rw [e]
    calc (b / 2 * t) ^ m * (2 / b) ^ m ≤ (Real.exp (b / 2 * t) * m.factorial) * (2 / b) ^ m :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by ring
  calc t ^ m * Real.exp (-b * t)
      ≤ (m.factorial * (2 / b) ^ m * Real.exp (b / 2 * t)) * Real.exp (-b * t) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (m.factorial * (2 / b) ^ m) * Real.exp (-(b / 2) * t) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

lemma integrable_pow_gauss (m : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : E4 => (‖x‖ ^ 2) ^ m * Real.exp (-b * ‖x‖ ^ 2)) := by
  refine ((integrable_gauss (b := b / 2) (by positivity)).const_mul
    (m.factorial * (2 / b) ^ m)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((continuous_norm.pow 2).pow m |>.mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_gauss_le m hb (by positivity)

/-- The integrand `e(-⟨x,ξ⟩) ‖x‖^{2k} e^{-a‖x‖²}`. -/
noncomputable def kern (ξ : E4) (k : ℕ) (a : ℝ) (x : E4) : ℂ :=
  (𝐞 (-⟪x, ξ⟫) : ℂ) * (((‖x‖ ^ 2) ^ k * Real.exp (-a * ‖x‖ ^ 2) : ℝ) : ℂ)

/-- `J ξ k a = 𝓕 (‖x‖^{2k} e^{-a‖x‖²}) ξ`. -/
noncomputable def J (ξ : E4) (k : ℕ) (a : ℝ) : ℂ := ∫ x, kern ξ k a x

lemma continuous_char (ξ : E4) : Continuous fun x : E4 => (𝐞 (-⟪x, ξ⟫) : ℂ) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).neg)

lemma continuous_kern (ξ : E4) (k : ℕ) (a : ℝ) : Continuous (kern ξ k a) :=
  (continuous_char ξ).mul (continuous_ofReal.comp ((continuous_norm.pow 2).pow k |>.mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))))

lemma norm_kern (ξ : E4) (k : ℕ) (a : ℝ) (x : E4) :
    ‖kern ξ k a x‖ = (‖x‖ ^ 2) ^ k * Real.exp (-a * ‖x‖ ^ 2) := by
  rw [kern, norm_mul, Circle.norm_coe, one_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

lemma kern_integrable (ξ : E4) (k : ℕ) {a : ℝ} (ha : 0 < a) : Integrable (kern ξ k a) :=
  (integrable_pow_gauss k ha).mono' (continuous_kern ξ k a).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (norm_kern ξ k a x).le)

lemma hasDerivAt_J (ξ : E4) (k : ℕ) {a0 : ℝ} (ha0 : 0 < a0) :
    HasDerivAt (J ξ k) (-J ξ (k + 1) a0) a0 := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun a x => kern ξ k a x) (F' := fun a x => -kern ξ (k + 1) a x) (x₀ := a0)
    (bound := fun x => (‖x‖ ^ 2) ^ (k + 1) * Real.exp (-(a0 / 2) * ‖x‖ ^ 2))
    (s := Metric.ball a0 (a0 / 2)) (Metric.ball_mem_nhds _ (by positivity))
    (Filter.Eventually.of_forall fun a => (continuous_kern ξ k a).aestronglyMeasurable)
    (kern_integrable ξ k ha0)
    ((continuous_kern ξ (k + 1) a0).aestronglyMeasurable.neg)
    (Filter.Eventually.of_forall fun x a ha => by
      rw [norm_neg, norm_kern]
      have h1 : a0 / 2 < a := by
        have := Metric.mem_ball.1 ha
        rw [Real.dist_eq] at this
        linarith [abs_lt.1 this]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
      nlinarith [sq_nonneg ‖x‖])
    (integrable_pow_gauss (k + 1) (by positivity))
    (Filter.Eventually.of_forall fun x a _ => by
      have hr : HasDerivAt (fun a : ℝ => (‖x‖ ^ 2) ^ k * Real.exp (-a * ‖x‖ ^ 2))
          ((‖x‖ ^ 2) ^ k * (Real.exp (-a * ‖x‖ ^ 2) * (-1 * ‖x‖ ^ 2))) a :=
        (((hasDerivAt_id a).neg.mul_const (‖x‖ ^ 2)).exp).const_mul _
      refine ((hr.ofReal_comp).const_mul (𝐞 (-⟪x, ξ⟫) : ℂ)).congr_deriv ?_
      simp only [kern]
      push_cast
      ring)
  have h2 := key.2
  simp only [integral_neg] at h2
  exact h2

lemma J_zero (ξ : E4) {a : ℝ} (ha : 0 < a) :
    J ξ 0 a = (Cf (Real.pi ^ 2 * ‖ξ‖ ^ 2) 0 a : ℂ) := by
  have h1 : J ξ 0 a = 𝓕 (fun v : E4 => cexp (-(a : ℂ) * ‖v‖ ^ 2)) ξ := by
    rw [J, Real.fourier_eq]
    congr 1
    funext x
    simp only [kern, pow_zero, one_mul, Circle.smul_def, smul_eq_mul]
    push_cast
    rfl
  rw [h1, fourier_gaussian_innerProductSpace (by simpa using ha), finrank_euclideanSpace_fin]
  have e : ((4 : ℕ) : ℂ) / 2 = ((2 : ℕ) : ℂ) := by norm_num
  rw [e, cpow_natCast]
  simp only [Cf, Q, eval_one, mul_one]
  push_cast
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [div_pow]
  congr 1
  · field_simp
  · congr 1
    field_simp

lemma J_eq_Cf (ξ : E4) : ∀ k : ℕ, ∀ a : ℝ, 0 < a → J ξ k a = (Cf (Real.pi ^ 2 * ‖ξ‖ ^ 2) k a : ℂ)
  | 0 => fun a ha => J_zero ξ ha
  | k + 1 => fun a ha => by
    have hJ := hasDerivAt_J ξ k ha
    have hC := (hasDerivAt_Cf (Real.pi ^ 2 * ‖ξ‖ ^ 2) k ha.ne').ofReal_comp
    have heq : J ξ k =ᶠ[nhds a] fun b => (Cf (Real.pi ^ 2 * ‖ξ‖ ^ 2) k b : ℂ) := by
      filter_upwards [Ioi_mem_nhds ha] with b hb using J_eq_Cf ξ k b hb
    have h := hJ.unique (hC.congr_of_eventuallyEq heq)
    push_cast at h
    exact neg_injective h

end D4Bound.FourierAux

namespace D4Bound

open MeasureTheory Complex D4Bound.FourierAux
open scoped FourierTransform RealInnerProductSpace

/-- `(-1)^j C(k, j) (k+1)!/(j+1)!`, the coefficient of `s^j` in the transform of `u^k e^{-u}`.
For `j ≤ k` it equals `(-1)^j k!/j! C(k+1, k-j)`. -/
noncomputable def lagR (k j : ℕ) : ℝ := FourierAux.lag k j

/-- Transform of one monomial: with `s = π²‖ξ‖²/2`,
`𝓕 (e^{-2‖x‖²} (2‖x‖²)^k) ξ = (π²/4) e^{-s} ∑_{j ≤ k} lagR k j s^j`. -/
theorem fourier_monomial (k : ℕ) (ξ : E4) :
    𝓕 (fun x : E4 => ((Real.exp (-2 * ‖x‖ ^ 2) * (2 * ‖x‖ ^ 2) ^ k : ℝ) : ℂ)) ξ =
      ((Real.pi ^ 2 / 4 * Real.exp (-(Real.pi ^ 2 / 2 * ‖ξ‖ ^ 2)) *
        ∑ j ∈ Finset.range (k + 1), lagR k j * (Real.pi ^ 2 / 2 * ‖ξ‖ ^ 2) ^ j : ℝ) : ℂ) := by
  have h1 : 𝓕 (fun x : E4 => ((Real.exp (-2 * ‖x‖ ^ 2) * (2 * ‖x‖ ^ 2) ^ k : ℝ) : ℂ)) ξ =
      ∫ x, (2 : ℂ) ^ k * kern ξ k 2 x := by
    rw [Real.fourier_eq]
    congr 1
    funext x
    simp only [kern, Circle.smul_def, smul_eq_mul]
    push_cast
    ring
  rw [h1, integral_const_mul, ← J, J_eq_Cf ξ k 2 two_pos, Cf, eval_Q]
  have e : Real.pi ^ 2 * ‖ξ‖ ^ 2 * 2⁻¹ = Real.pi ^ 2 / 2 * ‖ξ‖ ^ 2 := by ring
  rw [e]
  simp only [lagR]
  push_cast
  rw [inv_pow, pow_add]
  field_simp
  ring

/-- **Fourier identity for `e^{-2‖x‖²} F(2‖x‖²)`.** For a polynomial `F = ∑_{k ≤ d} c_k u^k`,
with `s = π²‖ξ‖²/2`,
`𝓕 (e^{-2‖x‖²} F(2‖x‖²)) ξ = (π²/4) e^{-s} G(s)`, `G(s) = ∑_{k ≤ d} c_k ∑_{j ≤ k} lagR k j s^j`.
Mathlib's convention: `𝓕 g ξ = ∫ e^{-2πi⟨x,ξ⟩} g x dx`. -/
theorem fourier_poly_gaussian (d : ℕ) (c : ℕ → ℝ) (ξ : E4) :
    𝓕 (fun x : E4 => ((Real.exp (-2 * ‖x‖ ^ 2) *
        ∑ k ∈ Finset.range (d + 1), c k * (2 * ‖x‖ ^ 2) ^ k : ℝ) : ℂ)) ξ =
      ((Real.pi ^ 2 / 4 * Real.exp (-(Real.pi ^ 2 / 2 * ‖ξ‖ ^ 2)) *
        ∑ k ∈ Finset.range (d + 1), c k *
          ∑ j ∈ Finset.range (k + 1), lagR k j * (Real.pi ^ 2 / 2 * ‖ξ‖ ^ 2) ^ j : ℝ) : ℂ) := by
  have hint : ∀ k, Integrable (fun x : E4 =>
      ((Real.exp (-2 * ‖x‖ ^ 2) * (2 * ‖x‖ ^ 2) ^ k : ℝ) : ℂ)) := by
    intro k
    refine ((integrable_pow_gauss k two_pos).const_mul (2 ^ k)).ofReal.congr
      (Filter.Eventually.of_forall fun x => ?_)
    show (((2 : ℝ) ^ k * ((‖x‖ ^ 2) ^ k * Real.exp (-2 * ‖x‖ ^ 2)) : ℝ) : ℂ) = _
    congr 1
    ring
  have h1 : 𝓕 (fun x : E4 => ((Real.exp (-2 * ‖x‖ ^ 2) *
        ∑ k ∈ Finset.range (d + 1), c k * (2 * ‖x‖ ^ 2) ^ k : ℝ) : ℂ)) ξ =
      ∑ k ∈ Finset.range (d + 1), (c k : ℂ) *
        𝓕 (fun x : E4 => ((Real.exp (-2 * ‖x‖ ^ 2) * (2 * ‖x‖ ^ 2) ^ k : ℝ) : ℂ)) ξ := by
    have hpt : ∀ v : E4, 𝐞 (-⟪v, ξ⟫) • ((Real.exp (-2 * ‖v‖ ^ 2) *
        ∑ k ∈ Finset.range (d + 1), c k * (2 * ‖v‖ ^ 2) ^ k : ℝ) : ℂ) =
        ∑ k ∈ Finset.range (d + 1), (c k : ℂ) *
          (𝐞 (-⟪v, ξ⟫) • ((Real.exp (-2 * ‖v‖ ^ 2) * (2 * ‖v‖ ^ 2) ^ k : ℝ) : ℂ)) := by
      intro v
      simp only [Circle.smul_def, smul_eq_mul]
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [Real.fourier_eq]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun k _ =>
      (((Real.fourierIntegral_convergent_iff ξ).2 (hint k)).const_mul (c k : ℂ))]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  rw [h1]
  simp_rw [fourier_monomial]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The function, its transform, and the transfer inputs -/

/-- `f(x) = e^{-2‖x‖²} F(2‖x‖²)` with `F(u) = ∑_{k ≤ d} c_k u^k`. -/
noncomputable def polyGauss (d : ℕ) (c : ℕ → ℝ) (x : E4) : ℝ :=
  Real.exp (-2 * ‖x‖ ^ 2) * ∑ k ∈ Finset.range (d + 1), c k * (2 * ‖x‖ ^ 2) ^ k

/-- `G(s) = ∑_{k ≤ d} c_k ∑_{j ≤ k} lagR k j s^j`. -/
noncomputable def lagG (d : ℕ) (c : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d + 1), c k * ∑ j ∈ Finset.range (k + 1), lagR k j * s ^ j

/-- `f̂(ξ) = (π²/4) e^{-s} G(s)`, `s = π²‖ξ‖²/2`. -/
noncomputable def polyGaussHat (d : ℕ) (c : ℕ → ℝ) (ξ : E4) : ℝ :=
  Real.pi ^ 2 / 4 * Real.exp (-(Real.pi ^ 2 / 2 * ‖ξ‖ ^ 2)) * lagG d c (Real.pi ^ 2 / 2 * ‖ξ‖ ^ 2)

theorem fourier_polyGauss (d : ℕ) (c : ℕ → ℝ) (ξ : E4) :
    𝓕 (fun x => (polyGauss d c x : ℂ)) ξ = (polyGaussHat d c ξ : ℂ) :=
  fourier_poly_gaussian d c ξ

theorem continuous_polyGauss (d : ℕ) (c : ℕ → ℝ) : Continuous (polyGauss d c) := by
  unfold polyGauss
  fun_prop

theorem integrable_polyGauss (d : ℕ) (c : ℕ → ℝ) : Integrable (polyGauss d c) := by
  have h : Integrable (fun x : E4 => ∑ k ∈ Finset.range (d + 1),
      (c k * 2 ^ k) * ((‖x‖ ^ 2) ^ k * Real.exp (-2 * ‖x‖ ^ 2))) :=
    integrable_finsetSum _ fun k _ => (integrable_pow_gauss k two_pos).const_mul _
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [polyGauss, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem integrable_polyGaussHat (d : ℕ) (c : ℕ → ℝ) : Integrable (polyGaussHat d c) := by
  have hb : (0 : ℝ) < Real.pi ^ 2 / 2 := by positivity
  have h : Integrable (fun ξ : E4 => ∑ k ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (k + 1),
      (Real.pi ^ 2 / 4 * c k * lagR k j * (Real.pi ^ 2 / 2) ^ j) *
        ((‖ξ‖ ^ 2) ^ j * Real.exp (-(Real.pi ^ 2 / 2) * ‖ξ‖ ^ 2))) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
      (integrable_pow_gauss j hb).const_mul _
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [polyGaussHat, lagG, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [neg_mul]
  ring

theorem integrable_fourier_polyGauss (d : ℕ) (c : ℕ → ℝ) :
    Integrable (𝓕 (fun x => (polyGauss d c x : ℂ))) := by
  have : 𝓕 (fun x => (polyGauss d c x : ℂ)) = fun ξ => (polyGaussHat d c ξ : ℂ) :=
    funext (fourier_polyGauss d c)
  rw [this]
  exact (integrable_polyGaussHat d c).ofReal

theorem re_fourier_polyGauss_nonneg (d : ℕ) (c : ℕ → ℝ)
    (hG : ∀ s : ℝ, 0 ≤ s → 0 ≤ lagG d c s) (ξ : E4) :
    0 ≤ (𝓕 (fun x => (polyGauss d c x : ℂ)) ξ).re := by
  rw [fourier_polyGauss, ofReal_re]
  exact mul_nonneg (by positivity) (hG _ (by positivity))

theorem integral_polyGauss (d : ℕ) (c : ℕ → ℝ) :
    ∫ x, polyGauss d c x = Real.pi ^ 2 / 4 * lagG d c 0 := by
  have h := fourier_polyGauss d c 0
  rw [Real.fourier_eq] at h
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul,
    integral_complex_ofReal] at h
  have h' : ∫ x, polyGauss d c x = polyGaussHat d c 0 := by exact_mod_cast h
  rw [h', polyGaussHat]
  simp

lemma lagR_zero (k : ℕ) : lagR k 0 = (k + 1).factorial := by
  simp [lagR, FourierAux.lag]

theorem lagG_zero (d : ℕ) (c : ℕ → ℝ) :
    lagG d c 0 = ∑ k ∈ Finset.range (d + 1), c k * (k + 1).factorial := by
  simp only [lagG]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [hj]) (by simp), lagR_zero]
  simp

/-- The paper's form of the coefficients: `lagR k j = (-1)^j k!/j! C(k+1, k-j)` for `j ≤ k`. -/
theorem lagR_eq {k j : ℕ} (hjk : j ≤ k) :
    lagR k j = (-1) ^ j * ((k.factorial : ℝ) / j.factorial) * ((k + 1).choose (k - j) : ℝ) := by
  have h1 : (k + 1) - (k - j) = j + 1 := by omega
  simp only [lagR, FourierAux.lag]
  rw [Nat.cast_choose ℝ hjk, Nat.cast_choose ℝ (by omega : k - j ≤ k + 1), h1]
  have : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos _
  have : (0 : ℝ) < (j + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have : (0 : ℝ) < (k - j).factorial := by exact_mod_cast Nat.factorial_pos _
  field_simp

theorem lagR_eq_zero {k j : ℕ} (hjk : k < j) : lagR k j = 0 := by
  simp [lagR, FourierAux.lag, Nat.choose_eq_zero_of_lt hjk]

/-- `G` in coefficient form: `G(s) = ∑_{j ≤ d} G_j s^j` with
`G_j = ∑_{k ≤ d, k ≥ j} c_k lagR k j`. -/
theorem lagG_eq_coeff (d : ℕ) (c : ℕ → ℝ) (s : ℝ) :
    lagG d c s = ∑ j ∈ Finset.range (d + 1),
      (∑ k ∈ Finset.range (d + 1), if j ≤ k then c k * lagR k j else 0) * s ^ j := by
  have h : ∀ k ∈ Finset.range (d + 1),
      c k * ∑ j ∈ Finset.range (k + 1), lagR k j * s ^ j =
        ∑ j ∈ Finset.range (d + 1), (if j ≤ k then c k * lagR k j else 0) * s ^ j := by
    intro k hk
    have hkd : k < d + 1 := Finset.mem_range.1 hk
    rw [Finset.mul_sum]
    calc ∑ j ∈ Finset.range (k + 1), c k * (lagR k j * s ^ j)
        = ∑ j ∈ Finset.range (d + 1), c k * (lagR k j * s ^ j) := by
          refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j _ hj => ?_
          rw [lagR_eq_zero (by simpa using hj)]
          ring
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs with hj
          · ring
          · rw [lagR_eq_zero (by omega)]
            ring
  rw [lagG, Finset.sum_congr rfl h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm

end D4Bound

