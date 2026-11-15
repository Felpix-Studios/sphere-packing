import D4Bound.CertificateIntervalTaylor

/-! Exact arithmetic of centered gradient/Hessian bounds, including signed diagonal terms. -/
namespace D4Bound.CertificateInterval

open Finset Set

def magnitude (I : Interval) : ℚ := max |I.lo| |I.hi|

lemma magnitude_nonneg (I : Interval) : 0 ≤ magnitude I :=
  (abs_nonneg I.lo).trans (le_max_left _ _)

lemma abs_le_magnitude {I : Interval} {x : ℝ} (hx : Contains I x) :
    |x| ≤ (magnitude I : ℝ) := by
  have hl : |(I.lo : ℝ)| ≤ (magnitude I : ℝ) := by
    exact_mod_cast (le_max_left |I.lo| |I.hi|)
  have hh : |(I.hi : ℝ)| ≤ (magnitude I : ℝ) := by
    exact_mod_cast (le_max_right |I.lo| |I.hi|)
  rw [abs_le] at hl hh ⊢
  exact ⟨hl.1.trans hx.1, hx.2.trans hh.2⟩

lemma abs_mul_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x*y| ≤ A*B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg y) ((abs_nonneg x).trans hx)

lemma signed_diagonal_lower {I : Interval} {H d R : ℝ}
    (hH : Contains I H) (hd : |d| ≤ R) :
    (min (I.lo : ℝ) 0)*R^2 ≤ H*d^2 := by
  have hm : min (I.lo : ℝ) 0 ≤ 0 := min_le_right _ _
  have hmH : min (I.lo : ℝ) 0 ≤ H := (min_le_left _ _).trans hH.1
  have hd2 : d^2 ≤ R^2 := by nlinarith [abs_nonneg d, (abs_le.mp hd).1, (abs_le.mp hd).2]
  calc (min (I.lo : ℝ) 0)*R^2 ≤ (min (I.lo : ℝ) 0)*d^2 :=
      mul_le_mul_of_nonpos_left hd2 hm
    _ ≤ H*d^2 := mul_le_mul_of_nonneg_right hmH (sq_nonneg d)

lemma mixed_lower {I : Interval} {H d e R S : ℝ}
    (hH : Contains I H) (hd : |d| ≤ R) (he : |e| ≤ S) :
    -(magnitude I : ℝ)*R*S ≤ H*d*e := by
  have hab := abs_mul_bound (abs_mul_bound (abs_le_magnitude hH) hd) he
  have hlow := (abs_le.mp hab).1
  nlinarith

structure CenteredData (n : ℕ) where
  center : Interval
  gradient : Fin n → Interval
  hessian : Fin n → Fin n → Interval
  radius : Fin n → ℚ

def entryLower {n : ℕ} (B : CenteredData n) (i j : Fin n) : ℚ :=
  if i = j then min (B.hessian i i).lo 0 * B.radius i ^ 2
  else -magnitude (B.hessian i j) * B.radius i * B.radius j

def centerLower {n : ℕ} (B : CenteredData n) : ℚ :=
  B.center.lo - ∑ i, magnitude (B.gradient i) * B.radius i +
    (∑ i, ∑ j, entryLower B i j)/2

lemma gradient_lower {n : ℕ} (B : CenteredData n) {g d : Fin n → ℝ}
    (hg : ∀ i, Contains (B.gradient i) (g i))
    (hd : ∀ i, |d i| ≤ (B.radius i : ℝ)) :
    -(∑ i, (magnitude (B.gradient i) : ℝ) * (B.radius i : ℝ)) ≤ ∑ i, g i*d i := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i hi
  exact (abs_le.mp (abs_mul_bound (abs_le_magnitude (hg i)) (hd i))).1

lemma hessian_lower {n : ℕ} (B : CenteredData n) {H : Fin n → Fin n → ℝ} {d : Fin n → ℝ}
    (hH : ∀ i j, Contains (B.hessian i j) (H i j))
    (hd : ∀ i, |d i| ≤ (B.radius i : ℝ)) :
    (∑ i, ∑ j, (entryLower B i j : ℝ)) ≤ ∑ i, ∑ j, H i j*d i*d j := by
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i = j
  · subst j
    simpa [entryLower, pow_two, mul_assoc] using signed_diagonal_lower (hH i i) (hd i)
  · simpa [entryLower, hij] using mixed_lower (hH i j) (hd i) (hd j)

/-- The rational centered lower bound is sound for any C2 path with these checked jets. -/
theorem centered_lower_sound {n : ℕ} (B : CenteredData n)
    {f : ℝ → ℝ} {g d : Fin n → ℝ} {H : ℝ → Fin n → Fin n → ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hg : HasDerivAt f (∑ i, g i*d i) 0)
    (hH : ∀ t ∈ Ioo (0 : ℝ) 1, iteratedDeriv 2 f t = ∑ i, ∑ j, H t i j*d i*d j)
    (hc : Contains B.center (f 0))
    (hgb : ∀ i, Contains (B.gradient i) (g i))
    (hHb : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i j, Contains (B.hessian i j) (H t i j))
    (hd : ∀ i, |d i| ≤ (B.radius i : ℝ)) :
    (centerLower B : ℝ) ≤ f 1 := by
  have hgrad := gradient_lower B hgb hd
  have hcurv : ∀ t ∈ Ioo (0 : ℝ) 1,
      (∑ i, ∑ j, (entryLower B i j : ℝ)) ≤ iteratedDeriv 2 f t := by
    intro t ht
    rw [hH t ht]
    exact hessian_lower B (hHb t ht) hd
  have hTaylor := taylor_lower_01 hf hg hcurv
  simp only [centerLower, Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_sum, Rat.cast_mul] at *
  linarith [hc.1]

def centeredOK {n : ℕ} (B : CenteredData n) : Bool := decide (0 ≤ centerLower B)

/-- The arithmetic acceptance condition is checked on exact rational data. -/
theorem centered_nonnegative {n : ℕ} (B : CenteredData n)
    {f : ℝ → ℝ} {g d : Fin n → ℝ} {H : ℝ → Fin n → Fin n → ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hg : HasDerivAt f (∑ i, g i*d i) 0)
    (hH : ∀ t ∈ Ioo (0 : ℝ) 1, iteratedDeriv 2 f t = ∑ i, ∑ j, H t i j*d i*d j)
    (hc : Contains B.center (f 0))
    (hgb : ∀ i, Contains (B.gradient i) (g i))
    (hHb : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i j, Contains (B.hessian i j) (H t i j))
    (hd : ∀ i, |d i| ≤ (B.radius i : ℝ))
    (hcheck : centeredOK B = true) : 0 ≤ f 1 := by
  have hq : 0 ≤ centerLower B := by simpa [centeredOK] using hcheck
  have hr : (0 : ℝ) ≤ (centerLower B : ℝ) := by exact_mod_cast hq
  exact hr.trans (centered_lower_sound B hf hg hH hc hgb hHb hd)

end D4Bound.CertificateInterval
