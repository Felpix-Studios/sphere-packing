import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# Shells and spherical codes

Elementary geometry used by the count domain (`CountDomain.lean`) and the graph slack
(`GraphSlack.lean`).

* `shell_inner_le`, the shell-to-sphere transfer: if `1 ≤ ‖x‖, ‖y‖ ≤ R` with `R² ≤ 2` and
  `‖x - y‖ ≥ 1`, then `⟪x, y⟫ ≤ (1 - 1/(2R²)) ‖x‖ ‖y‖`.
* `annulus_inner_le`: if `33/28 ≤ ‖x‖, ‖y‖ ≤ 7/4` and `‖x - y‖ ≥ 1`, then
  `⟪x, y⟫ ≤ (41/49) ‖x‖ ‖y‖`.
* `SphericalCodeBound s m`: every set of unit vectors in `ℝ⁴` with pairwise inner products at
  most `s` has at most `m` elements. This is the statement that an exact Delsarte certificate
  proves; it is a hypothesis, not proved here.
* `card_le_of_cos_le`: a finite set of nonzero vectors with pairwise cosines at most `ρ < 1`
  has at most `m` elements when `SphericalCodeBound ρ m` holds (the map to directions is
  injective).
-/

open Finset
open scoped RealInnerProductSpace

namespace D4Bound

section general

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The law of cosines with a separation: `2⟪x, y⟫ ≤ ‖x‖² + ‖y‖² - 1` when `‖x - y‖ ≥ 1`. -/
lemma two_inner_le_of_sep {x y : V} (hsep : 1 ≤ ‖x - y‖) :
    2 * ⟪x, y⟫ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 - 1 := by
  have h := norm_sub_sq_real x y
  have h1 : 1 ≤ ‖x - y‖ ^ 2 := by nlinarith
  linarith

/-- Scalar form of the shell-to-sphere transfer: on `[1, R]²` with `R² ≤ 2`,
`R² (r² + s² - 1) ≤ (2R² - 1) r s`. -/
lemma shell_scalar {R r s : ℝ} (hr : 1 ≤ r) (hrR : r ≤ R) (hs : 1 ≤ s) (hsR : s ≤ R)
    (hR2 : R ^ 2 ≤ 2) :
    R ^ 2 * (r ^ 2 + s ^ 2 - 1) ≤ (2 * R ^ 2 - 1) * (r * s) := by
  have hR : 1 ≤ R := hr.trans hrR
  -- `(r² + s² - 1)/(2rs)` increases in `r`: `R (r² + s² - 1) ≤ r (R² + s² - 1)`.
  have hA : R * (r ^ 2 + s ^ 2 - 1) ≤ r * (R ^ 2 + s ^ 2 - 1) := by
    have h1 : s ^ 2 - 1 - r * R ≤ 0 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (neg_nonneg.mpr h1)]
  -- and in `s`: `R (R² + s² - 1) ≤ s (2R² - 1)`.
  have hB : R * (R ^ 2 + s ^ 2 - 1) ≤ s * (2 * R ^ 2 - 1) := by
    have h1 : 0 ≤ 1 - R ^ 2 + R * s := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hsR) h1]
  have hR0 : 0 ≤ R := by linarith
  have hr0 : 0 ≤ r := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hA hR0, mul_le_mul_of_nonneg_left hB hr0]

/-- **Shell-to-sphere transfer.** If `1 ≤ ‖x‖, ‖y‖ ≤ R` with `R² ≤ 2` and `‖x - y‖ ≥ 1`, then
the cosine of the angle between `x` and `y` is at most `1 - 1/(2R²)`. -/
theorem shell_inner_le {R : ℝ} {x y : V} (hx : 1 ≤ ‖x‖) (hxR : ‖x‖ ≤ R) (hy : 1 ≤ ‖y‖)
    (hyR : ‖y‖ ≤ R) (hR2 : R ^ 2 ≤ 2) (hsep : 1 ≤ ‖x - y‖) :
    ⟪x, y⟫ ≤ (1 - 1 / (2 * R ^ 2)) * (‖x‖ * ‖y‖) := by
  have hR : 1 ≤ R := hx.trans hxR
  have hRpos : 0 < R ^ 2 := by positivity
  have h1 := two_inner_le_of_sep hsep
  have h2 := shell_scalar hx hxR hy hyR hR2
  have : (1 - 1 / (2 * R ^ 2)) * (‖x‖ * ‖y‖) =
      (2 * R ^ 2 - 1) * (‖x‖ * ‖y‖) / (2 * R ^ 2) := by field_simp
  rw [this, le_div_iff₀ (by positivity)]
  nlinarith

/-- Scalar form of the two-shell bound: for `ρ ∈ [1, r]`, `σ ∈ [1, R]` with `r², R² ≤ 2`,
`r R (ρ² + σ² - 1) ≤ (r² + R² - 1) ρ σ`. -/
lemma two_shell_scalar {r R ρ σ : ℝ} (hρ : 1 ≤ ρ) (hρr : ρ ≤ r) (hσ : 1 ≤ σ) (hσR : σ ≤ R)
    (hr2 : r ^ 2 ≤ 2) (hR2 : R ^ 2 ≤ 2) :
    r * R * (ρ ^ 2 + σ ^ 2 - 1) ≤ (r ^ 2 + R ^ 2 - 1) * (ρ * σ) := by
  have hr : 1 ≤ r := hρ.trans hρr
  have hR : 1 ≤ R := hσ.trans hσR
  -- `(ρ² + σ² - 1)/(2ρσ)` increases in `ρ`: `r (ρ² + σ² - 1) ≤ ρ (r² + σ² - 1)`.
  have hA : r * (ρ ^ 2 + σ ^ 2 - 1) ≤ ρ * (r ^ 2 + σ ^ 2 - 1) := by
    have h1 : σ ^ 2 - 1 - ρ * r ≤ 0 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hρr) (neg_nonneg.mpr h1)]
  -- and in `σ`: `R (r² + σ² - 1) ≤ σ (r² + R² - 1)`.
  have hB : R * (r ^ 2 + σ ^ 2 - 1) ≤ σ * (r ^ 2 + R ^ 2 - 1) := by
    have h1 : 0 ≤ σ * R + 1 - r ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hσR) h1]
  have hR0 : 0 ≤ R := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hA hR0, mul_le_mul_of_nonneg_left hB hρ0]

/-- **Two-shell transfer.** If `1 ≤ ‖x‖ ≤ r`, `1 ≤ ‖y‖ ≤ R` with `r², R² ≤ 2` and
`‖x - y‖ ≥ 1`, the cosine of the angle between `x` and `y` is at most
`(r² + R² - 1)/(2rR)`. -/
theorem two_shell_inner_le {r R : ℝ} {x y : V} (hx : 1 ≤ ‖x‖) (hxr : ‖x‖ ≤ r) (hy : 1 ≤ ‖y‖)
    (hyR : ‖y‖ ≤ R) (hr2 : r ^ 2 ≤ 2) (hR2 : R ^ 2 ≤ 2) (hsep : 1 ≤ ‖x - y‖) :
    ⟪x, y⟫ ≤ (r ^ 2 + R ^ 2 - 1) / (2 * r * R) * (‖x‖ * ‖y‖) := by
  have hr : 0 < r := by linarith
  have hR : 0 < R := by linarith
  have h1 := two_inner_le_of_sep hsep
  have h2 := two_shell_scalar hx hxr hy hyR hr2 hR2
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ r * R)]

/-- Scalar form of the annulus bound: on `[33/28, 7/4]²`, `49(r² + s² - 1) ≤ 82 r s`. The
corner values of `(r² + s² - 1)/(2rs)` are `697/1089` and `41/49`. -/
lemma annulus_scalar {r s : ℝ} (hr : 33 / 28 ≤ r) (hr' : r ≤ 7 / 4) (hs : 33 / 28 ≤ s)
    (hs' : s ≤ 7 / 4) : 49 * (r ^ 2 + s ^ 2 - 1) ≤ 82 * (r * s) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hs),
    mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hs'),
    mul_nonneg (sub_nonneg.mpr hr') (sub_nonneg.mpr hs),
    mul_nonneg (sub_nonneg.mpr hr') (sub_nonneg.mpr hs'),
    mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr'),
    mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hs')]

/-- Separated points of the annulus `33/28 ≤ ‖·‖ ≤ 7/4` have cosine at most `41/49`. -/
theorem annulus_inner_le {x y : V} (hx : 33 / 28 ≤ ‖x‖) (hx' : ‖x‖ ≤ 7 / 4) (hy : 33 / 28 ≤ ‖y‖)
    (hy' : ‖y‖ ≤ 7 / 4) (hsep : 1 ≤ ‖x - y‖) :
    ⟪x, y⟫ ≤ 41 / 49 * (‖x‖ * ‖y‖) := by
  have h1 := two_inner_le_of_sep hsep
  have h2 := annulus_scalar hx hx' hy hy'
  nlinarith

/-- The direction `x/‖x‖`. -/
noncomputable def dir (x : V) : V := ‖x‖⁻¹ • x

lemma norm_dir {x : V} (hx : x ≠ 0) : ‖dir x‖ = 1 := norm_smul_inv_norm hx

lemma inner_dir (x y : V) : ⟪dir x, dir y⟫ = ⟪x, y⟫ / (‖x‖ * ‖y‖) := by
  rw [dir, dir, real_inner_smul_left, real_inner_smul_right]
  field_simp

/-- If distinct points have cosine at most `ρ < 1`, their directions are distinct and have
inner product at most `ρ`. -/
lemma dir_injOn {X : Finset V} {ρ : ℝ} (hρ : ρ < 1) (h0 : ∀ x ∈ X, x ≠ 0)
    (hcos : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ⟪x, y⟫ ≤ ρ * (‖x‖ * ‖y‖)) :
    Set.InjOn dir (X : Set V) := by
  intro x hx y hy hxy
  by_contra hne
  have h := hcos x hx y hy hne
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr (h0 x hx)
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr (h0 y hy)
  have h1 : ⟪dir x, dir y⟫ = 1 := by
    rw [hxy, real_inner_self_eq_norm_sq, norm_dir (h0 y hy)]; norm_num
  rw [inner_dir, div_eq_one_iff_eq (by positivity)] at h1
  nlinarith [mul_pos hx0 hy0]

lemma inner_dir_le {x y : V} {ρ : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ⟪x, y⟫ ≤ ρ * (‖x‖ * ‖y‖)) : ⟪dir x, dir y⟫ ≤ ρ := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  rw [inner_dir, div_le_iff₀ (by positivity)]
  exact h

end general

/-! ## Spherical code bounds in `ℝ⁴` -/

/-- `A(4, s) ≤ m`: every finite set of unit vectors in `ℝ⁴` whose distinct members have inner
product at most `s` has at most `m` elements. -/
def SphericalCodeBound (s : ℝ) (m : ℕ) : Prop :=
  ∀ C : Finset (EuclideanSpace ℝ (Fin 4)), (∀ u ∈ C, ‖u‖ = 1) →
    (∀ u ∈ C, ∀ v ∈ C, u ≠ v → ⟪u, v⟫ ≤ s) → C.card ≤ m

/-- A finite set of nonzero vectors in `ℝ⁴` with pairwise cosines at most `ρ < 1` has at most
`m` elements, given `A(4, ρ) ≤ m`. -/
theorem card_le_of_cos_le {X : Finset (EuclideanSpace ℝ (Fin 4))} {ρ : ℝ} {m : ℕ}
    (hcode : SphericalCodeBound ρ m) (hρ : ρ < 1) (h0 : ∀ x ∈ X, x ≠ 0)
    (hcos : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ⟪x, y⟫ ≤ ρ * (‖x‖ * ‖y‖)) : X.card ≤ m := by
  classical
  have hinj := dir_injOn hρ h0 hcos
  rw [← Finset.card_image_of_injOn hinj]
  apply hcode
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact norm_dir (h0 x hx)
  · intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    have hxy : x ≠ y := fun h => huv (by rw [h])
    exact inner_dir_le (h0 x hx) (h0 y hy) (hcos x hx y hy hxy)

/-- Monotonicity of code bounds in the cutoff. -/
lemma SphericalCodeBound.mono {s s' : ℝ} {m : ℕ} (h : SphericalCodeBound s m) (hs : s' ≤ s) :
    SphericalCodeBound s' m :=
  fun C hu hc => h C hu fun u hu' v hv huv => (hc u hu' v hv huv).trans hs

end D4Bound
