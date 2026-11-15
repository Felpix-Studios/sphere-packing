import D4Bound.CertificateInterval

/-! Exact exponential enclosures from the proved Taylor remainder bound. -/
namespace D4Bound.CertificateInterval

open Finset

def expTaylor (q : ℚ) (n : ℕ) : ℚ :=
  ∑ m ∈ range n, q ^ m / m.factorial

def expRemainder (q : ℚ) (n : ℕ) : ℚ :=
  |q| ^ n * ((n + 1 : ℕ) : ℚ) / ((n.factorial : ℚ) * n)

def expOK (n : ℕ) (A B : Interval) : Bool := decide
  (0 < n ∧ -1 ≤ A.lo ∧ A.hi ≤ 1 ∧
   B.lo ≤ expTaylor A.lo n - expRemainder A.lo n ∧
   expTaylor A.hi n + expRemainder A.hi n ≤ B.hi)

lemma cast_expTaylor (q : ℚ) (n : ℕ) :
    (expTaylor q n : ℝ) = ∑ m ∈ range n, (q : ℝ) ^ m / m.factorial := by
  simp [expTaylor]

lemma cast_expRemainder (q : ℚ) (n : ℕ) :
    (expRemainder q n : ℝ) = |(q : ℝ)| ^ n * ((n + 1 : ℕ) : ℝ) /
      ((n.factorial : ℝ) * n) := by
  simp [expRemainder]

lemma exp_endpoint_bounds {q : ℚ} {n : ℕ} (hq : |q| ≤ 1) (hn : 0 < n) :
    ((expTaylor q n - expRemainder q n : ℚ) : ℝ) ≤ Real.exp q ∧
    Real.exp q ≤ ((expTaylor q n + expRemainder q n : ℚ) : ℝ) := by
  have hqr : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
  have h := Real.exp_bound hqr hn
  rw [abs_le] at h
  simp only [Nat.succ_eq_add_one, ← mul_div_assoc] at h
  rw [Rat.cast_sub, Rat.cast_add, cast_expTaylor, cast_expRemainder]
  constructor <;> linarith [h.1,h.2]

lemma exp_sound {n : ℕ} {A B : Interval} {x : ℝ}
    (h : expOK n A B = true) (hx : Contains A x) : Contains B (Real.exp x) := by
  have hq : 0 < n ∧ -1 ≤ A.lo ∧ A.hi ≤ 1 ∧
      B.lo ≤ expTaylor A.lo n - expRemainder A.lo n ∧
      expTaylor A.hi n + expRemainder A.hi n ≤ B.hi := by simpa [expOK] using h
  have horder : A.lo ≤ A.hi := by exact_mod_cast hx.1.trans hx.2
  have ha : |A.lo| ≤ 1 := abs_le.mpr ⟨hq.2.1, horder.trans hq.2.2.1⟩
  have hb : |A.hi| ≤ 1 := abs_le.mpr ⟨hq.2.1.trans horder, hq.2.2.1⟩
  have ea := exp_endpoint_bounds ha hq.1
  have eb := exp_endpoint_bounds hb hq.1
  have hl : (B.lo : ℝ) ≤ ((expTaylor A.lo n - expRemainder A.lo n : ℚ) : ℝ) := by
    exact_mod_cast hq.2.2.2.1
  have hu : ((expTaylor A.hi n + expRemainder A.hi n : ℚ) : ℝ) ≤ (B.hi : ℝ) := by
    exact_mod_cast hq.2.2.2.2
  exact ⟨hl.trans (ea.1.trans (Real.exp_le_exp.mpr hx.1)),
    (Real.exp_le_exp.mpr hx.2).trans (eb.2.trans hu)⟩

/-- Range reduction avoids needing an exponential checker outside [-1,1]. -/
lemma exp_div_nat_pow (x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    Real.exp (x / n) ^ n = Real.exp x := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp

end D4Bound.CertificateInterval

namespace D4Bound.CertificateInterval

def divideInterval (A : Interval) (k : ℕ) : Interval := ⟨A.lo / k, A.hi / k⟩

def expScaledOK (degree scale : ℕ) (E A B : Interval) : Bool := decide (0 < scale ∧
    0 ≤ E.lo ∧ B.lo ≤ E.lo ^ scale ∧ E.hi ^ scale ≤ B.hi) &&
    expOK degree (divideInterval A scale) E

lemma exp_scaled_sound {degree scale : ℕ} {E A B : Interval} {x : ℝ}
    (h : expScaledOK degree scale E A B = true) (hx : Contains A x) :
    Contains B (Real.exp x) := by
  have hh : (0 < scale ∧ 0 ≤ E.lo ∧ B.lo ≤ E.lo ^ scale ∧ E.hi ^ scale ≤ B.hi) ∧
      expOK degree (divideInterval A scale) E = true := by simpa [expScaledOK] using h
  have hs : (0 : ℝ) < scale := by exact_mod_cast hh.1.1
  have hdiv : Contains (divideInterval A scale) (x / scale) := by
    constructor
    · simpa [divideInterval] using div_le_div_of_nonneg_right hx.1 hs.le
    · simpa [divideInterval] using div_le_div_of_nonneg_right hx.2 hs.le
  have he := exp_sound hh.2 hdiv
  have hE0 : (0 : ℝ) ≤ E.lo := by exact_mod_cast hh.1.2.1
  have hlo : (B.lo : ℝ) ≤ (E.lo : ℝ) ^ scale := by exact_mod_cast hh.1.2.2.1
  have hhi : (E.hi : ℝ) ^ scale ≤ (B.hi : ℝ) := by exact_mod_cast hh.1.2.2.2
  have hp := exp_div_nat_pow x (Nat.ne_of_gt hh.1.1)
  constructor
  · rw [← hp]
    exact hlo.trans (pow_le_pow_left₀ hE0 he.1 _)
  · rw [← hp]
    exact (pow_le_pow_left₀ (Real.exp_nonneg _) he.2 _).trans hhi

end D4Bound.CertificateInterval
