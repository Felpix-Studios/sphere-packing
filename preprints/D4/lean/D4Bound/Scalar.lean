import D4Bound.ScalarCert
import D4Bound.Density
import D4Bound.Fourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The scalar function

`F` and `G` are the degree-49 polynomials of `data/v7/scalar.json`, and

  `f(x) = exp(-2‖x‖²) F(2‖x‖²)`,   `f̂(ξ) = (π²/4) exp(-s) G(s)`,   `s = π²‖ξ‖²/2`.

Proved here, by exact computation in the kernel (`ScalarCert.lean`) and short real analysis:

* `coeff_identity`: `G_j = ∑_{k ≥ j} F_k (-1)^j k!/j! C(k+1, k-j)`, the coefficient form of the
  Fourier identity;
* `G_zero`: `G(0) = 1`; `G_pos`: `G(s) > 0` for `s ≥ 0`; `F_neg`: `F(t) < 0` for `t ≥ 49/8`;
* `f_nonpos`: `f(x) ≤ 0` for `‖x‖ ≥ 7/4`; `f_continuous`, `f_integrable`.

`fourierIdentity` proves `𝓕 f = f̂` from the generic theorem `fourier_polyGauss` of
`Fourier.lean` and the coefficient identity. `fourier_integrable`, `fourier_re_nonneg` and
`integral_f` then give the remaining inputs of the density transfer theorem.
-/

open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace

namespace D4Bound

/-! ## Polynomials -/

/-- Horner evaluation of a rational coefficient list, constant term first. -/
noncomputable def evalQ : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * evalQ cs x

/-- The polynomial `F` of degree 49. -/
noncomputable def F (t : ℝ) : ℝ := evalQ Fq t

/-- The polynomial `G` of degree 49. -/
noncomputable def G (s : ℝ) : ℝ := evalQ Gq s

lemma evalQ_map_div (l : List ℤ) (D : ℕ) (x : ℝ) :
    evalQ (l.map fun z : ℤ => (z : ℚ) / D) x = evalZ l x / D := by
  induction l with
  | nil => simp [evalQ, evalZ]
  | cons c cs ih => simp only [List.map, evalQ, evalZ, ih]; push_cast; ring

lemma evalZ_map_neg (l : List ℤ) (x : ℝ) : evalZ (l.map (- ·)) x = -evalZ l x := by
  induction l with
  | nil => simp [evalZ]
  | cons c cs ih => simp only [List.map, evalZ, ih]; push_cast; ring

theorem Fq_eq : Fq = FZ.map (fun z : ℤ => (z : ℚ) / DF) := by decide +kernel

theorem Gq_eq : Gq = GZ.map (fun z : ℤ => (z : ℚ) / DG) := by decide +kernel

lemma F_eq (t : ℝ) : F t = evalZ FZ t / DF := by rw [F, Fq_eq, evalQ_map_div]

lemma G_eq (s : ℝ) : G s = evalZ GZ s / DG := by rw [G, Gq_eq, evalQ_map_div]

lemma DF_pos : (0 : ℝ) < DF := by norm_num [DF]

lemma DG_pos : (0 : ℝ) < DG := by norm_num [DG]

/-- The coefficient form of the Fourier identity:
`G_j = ∑_{k ≥ j} F_k (-1)^j k!/j! C(k+1, k-j)` for `j < 50`, and both lists have 50 entries. -/
theorem coeff_identity : Fq.length = 50 ∧ Gq.length = 50 ∧
    ∀ j < 50, Gq.getD j 0 =
      ((List.range 50).map fun k => if j ≤ k then Fq.getD k 0 * lagCoeff k j else 0).sum := by
  decide +kernel

theorem Gq_head : Gq = 1 :: Gq.tail := by decide +kernel

theorem G_zero : G 0 = 1 := by
  rw [G, Gq_head, evalQ]; simp

/-- `G(s) > 0` for every `s ≥ 0`. -/
theorem G_pos {s : ℝ} (hs : 0 ≤ s) : 0 < G s := by
  rw [G_eq]
  refine div_pos ?_ DG_pos
  rcases lt_or_ge s 256 with h | h
  · exact G_cover s (by simpa using hs) (by simpa using h)
  · exact tailOK_sound G_tail s (by exact_mod_cast h)

/-- `F(t) < 0` for every `t ≥ 49/8`. -/
theorem F_neg {t : ℝ} (ht : 49 / 8 ≤ t) : F t < 0 := by
  rw [F_eq]
  refine div_neg_of_neg_of_pos ?_ DF_pos
  have : 0 < evalZ negFZ t := by
    rcases lt_or_ge t 128 with h | h
    · exact F_cover t (by norm_num; linarith) (by simpa using h)
    · exact tailOK_sound F_tail t (by exact_mod_cast h)
  rw [negFZ, evalZ_map_neg] at this
  linarith

/-! ## Growth bounds -/

lemma evalQ_eq_sum (l : List ℚ) (t : ℝ) :
    evalQ l t = ∑ i ∈ Finset.range l.length, ((l.getD i 0 : ℚ) : ℝ) * t ^ i := by
  induction l with
  | nil => simp [evalQ]
  | cons c cs ih =>
    rw [evalQ, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- The constant in `|p(t)| ≤ M e^{t/2}`. -/
noncomputable def growth (l : List ℚ) : ℝ :=
  ∑ i ∈ Finset.range l.length, |((l.getD i 0 : ℚ) : ℝ)| * (i.factorial * 2 ^ i)

lemma abs_evalQ_le (l : List ℚ) {t : ℝ} (ht : 0 ≤ t) :
    |evalQ l t| ≤ growth l * Real.exp (t / 2) := by
  rw [evalQ_eq_sum, growth, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (pow_nonneg ht i), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := Real.pow_div_factorial_le_exp (x := t / 2) (by linarith) i
  have hf : (0 : ℝ) < i.factorial := by exact_mod_cast Nat.factorial_pos i
  rw [div_le_iff₀ hf, div_pow] at h
  have h2 : (0 : ℝ) < 2 ^ i := by positivity
  calc t ^ i = t ^ i / 2 ^ i * 2 ^ i := by field_simp
    _ ≤ Real.exp (t / 2) * i.factorial * 2 ^ i := by gcongr
    _ = i.factorial * 2 ^ i * Real.exp (t / 2) := by ring

lemma integrable_gaussian {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : E4 => Real.exp (-c * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E4) (b := (c : ℂ)) (by simpa using hc) 0
    0).norm
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [inner_zero_left, ofReal_zero, mul_zero, add_zero]
  rw [Complex.norm_exp]
  congr 1
  simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  norm_cast

lemma continuous_evalQ (l : List ℚ) : Continuous (evalQ l) := by
  induction l with
  | nil => exact continuous_const
  | cons c cs ih =>
    simp only [evalQ]
    exact continuous_const.add (continuous_id.mul ih)

/-- `x ↦ p(c‖x‖²) e^{-c‖x‖²}` is integrable on `ℝ⁴` for `c > 0`. -/
lemma integrable_poly_gaussian (l : List ℚ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : E4 => evalQ l (c * ‖x‖ ^ 2) * Real.exp (-(c * ‖x‖ ^ 2))) := by
  have hg := (integrable_gaussian (c := c / 2) (by linarith)).const_mul (growth l)
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((continuous_evalQ l).comp (continuous_const.mul (continuous_norm.pow 2))).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)).neg)
      |>.aestronglyMeasurable
  · have ht : 0 ≤ c * ‖x‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |evalQ l (c * ‖x‖ ^ 2)| * Real.exp (-(c * ‖x‖ ^ 2))
        ≤ growth l * Real.exp (c * ‖x‖ ^ 2 / 2) * Real.exp (-(c * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_right (abs_evalQ_le l ht) (Real.exp_pos _).le
      _ = growth l * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-! ## The function `f` and its transform -/

/-- The scalar function `f(x) = exp(-2‖x‖²) F(2‖x‖²)`. -/
noncomputable def f (x : E4) : ℝ := Real.exp (-2 * ‖x‖ ^ 2) * F (2 * ‖x‖ ^ 2)

/-- The claimed transform `f̂(ξ) = (π²/4) exp(-s) G(s)` with `s = π²‖ξ‖²/2`. -/
noncomputable def fhat (ξ : E4) : ℝ :=
  Real.pi ^ 2 / 4 * Real.exp (-(Real.pi ^ 2 / 2 * ‖ξ‖ ^ 2)) * G (Real.pi ^ 2 / 2 * ‖ξ‖ ^ 2)

/-- The Fourier identity `𝓕 f = f̂`, with `𝓕 g (ξ) = ∫ g(x) e^{-2πi⟨x,ξ⟩} dx`. -/
def FourierIdentity : Prop := ∀ ξ : E4, 𝓕 (fun x => (f x : ℂ)) ξ = (fhat ξ : ℂ)

theorem f_zero : f 0 = F 0 := by simp [f]

theorem f_nonpos {x : E4} (hx : 7 / 4 ≤ ‖x‖) : f x ≤ 0 := by
  have h : 49 / 8 ≤ 2 * ‖x‖ ^ 2 := by nlinarith
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (F_neg h).le

theorem f_continuous : Continuous f :=
  (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))).mul
    ((continuous_evalQ Fq).comp (continuous_const.mul (continuous_norm.pow 2)))

theorem f_integrable : Integrable f := by
  refine (integrable_poly_gaussian Fq (c := 2) (by norm_num)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [f, F]; ring_nf

theorem fhat_integrable : Integrable fhat := by
  have hc : 0 < Real.pi ^ 2 / 2 := by positivity
  refine ((integrable_poly_gaussian Gq hc).const_mul (Real.pi ^ 2 / 4)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [fhat, G]; ring

theorem fhat_pos (ξ : E4) : 0 < fhat ξ := by
  unfold fhat
  have := G_pos (s := Real.pi ^ 2 / 2 * ‖ξ‖ ^ 2) (by positivity)
  positivity

theorem fhat_zero : fhat 0 = Real.pi ^ 2 / 4 := by simp [fhat, G_zero]

theorem fourier_integrable (hF : FourierIdentity) :
    Integrable (𝓕 (fun x => (f x : ℂ))) := by
  have : 𝓕 (fun x => (f x : ℂ)) = fun ξ => (fhat ξ : ℂ) := funext hF
  rw [this]
  exact fhat_integrable.ofReal

theorem fourier_re_nonneg (hF : FourierIdentity) (ξ : E4) :
    0 ≤ (𝓕 (fun x => (f x : ℂ)) ξ).re := by
  rw [hF ξ, ofReal_re]; exact (fhat_pos ξ).le

theorem integral_f (hF : FourierIdentity) : ∫ x, f x = Real.pi ^ 2 / 4 := by
  have h := hF 0
  rw [Real.fourier_eq] at h
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul,
    integral_complex_ofReal, fhat_zero] at h
  exact_mod_cast h

/-! ## The Fourier identity, from `Fourier.lean` -/

/-- `coeff_identity` with a `Finset` sum. -/
theorem coeff_identity' : ∀ j < 50, Gq.getD j 0 =
    ∑ k ∈ Finset.range 50, if j ≤ k then Fq.getD k 0 * lagCoeff k j else 0 := by
  decide +kernel

/-- The coefficients of `F` as a function `ℕ → ℝ`. -/
noncomputable def cF (k : ℕ) : ℝ := ((Fq.getD k 0 : ℚ) : ℝ)

lemma f_eq_polyGauss : f = polyGauss 49 cF := by
  funext x
  rw [f, F, evalQ_eq_sum, coeff_identity.1, polyGauss]
  rfl

lemma lagCoeff_cast {k j : ℕ} (hjk : j ≤ k) : ((lagCoeff k j : ℚ) : ℝ) = lagR k j := by
  rw [lagR_eq hjk, lagCoeff]; push_cast; ring

lemma G_eq_lagG (s : ℝ) : G s = lagG 49 cF s := by
  rw [G, evalQ_eq_sum, coeff_identity.2.1, lagG_eq_coeff]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [coeff_identity' j (Finset.mem_range.mp hj), Rat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hjk
  · rw [Rat.cast_mul, lagCoeff_cast hjk]; rfl
  · simp

lemma fhat_eq_polyGaussHat : fhat = polyGaussHat 49 cF := by
  funext ξ
  rw [fhat, polyGaussHat, G_eq_lagG]

/-- The Fourier identity `𝓕 f = f̂`, from `fourier_polyGauss` and the coefficient identity. -/
theorem fourierIdentity : FourierIdentity := by
  intro ξ
  rw [f_eq_polyGauss, fhat_eq_polyGaussHat]
  exact fourier_polyGauss 49 cF ξ

end D4Bound
