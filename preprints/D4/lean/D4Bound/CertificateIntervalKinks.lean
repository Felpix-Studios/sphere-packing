import D4Bound.CertificateInterval

/-! Certified bounds for closed and open indicators and monotone lower substitutions. -/
namespace D4Bound.CertificateInterval

noncomputable def indicatorLE (x : ℝ) : ℝ := if x ≤ 0 then 1 else 0
noncomputable def indicatorLT (x : ℝ) : ℝ := if x < 0 then 1 else 0

def indicatorLEOK (A B : Interval) : Bool := decide
  ((B.lo ≤ 0 ∧ 1 ≤ B.hi) ∨
   (A.hi ≤ 0 ∧ B.lo ≤ 1 ∧ 1 ≤ B.hi) ∨
   (0 < A.lo ∧ B.lo ≤ 0 ∧ 0 ≤ B.hi))

def indicatorLTOK (A B : Interval) : Bool := decide
  ((B.lo ≤ 0 ∧ 1 ≤ B.hi) ∨
   (A.hi < 0 ∧ B.lo ≤ 1 ∧ 1 ≤ B.hi) ∨
   (0 ≤ A.lo ∧ B.lo ≤ 0 ∧ 0 ≤ B.hi))

lemma indicatorLE_sound {A B : Interval} {x : ℝ}
    (h : indicatorLEOK A B = true) (hx : Contains A x) : Contains B (indicatorLE x) := by
  have hq : (B.lo ≤ 0 ∧ 1 ≤ B.hi) ∨
      (A.hi ≤ 0 ∧ B.lo ≤ 1 ∧ 1 ≤ B.hi) ∨
      (0 < A.lo ∧ B.lo ≤ 0 ∧ 0 ≤ B.hi) := by simpa [indicatorLEOK] using h
  have hr : ((B.lo : ℝ) ≤ 0 ∧ 1 ≤ (B.hi : ℝ)) ∨
      ((A.hi : ℝ) ≤ 0 ∧ (B.lo : ℝ) ≤ 1 ∧ 1 ≤ (B.hi : ℝ)) ∨
      (0 < (A.lo : ℝ) ∧ (B.lo : ℝ) ≤ 0 ∧ 0 ≤ (B.hi : ℝ)) := by exact_mod_cast hq
  rcases hr with h | h | h
  · unfold Contains indicatorLE; split_ifs <;> constructor <;> linarith [h.1,h.2]
  · have hh : x ≤ 0 := hx.2.trans h.1
    simpa [indicatorLE, hh, Contains] using h.2
  · have hh : ¬x ≤ 0 := not_le.mpr (h.1.trans_le hx.1)
    simpa [indicatorLE, hh, Contains] using h.2

lemma indicatorLT_sound {A B : Interval} {x : ℝ}
    (h : indicatorLTOK A B = true) (hx : Contains A x) : Contains B (indicatorLT x) := by
  have hq : (B.lo ≤ 0 ∧ 1 ≤ B.hi) ∨
      (A.hi < 0 ∧ B.lo ≤ 1 ∧ 1 ≤ B.hi) ∨
      (0 ≤ A.lo ∧ B.lo ≤ 0 ∧ 0 ≤ B.hi) := by simpa [indicatorLTOK] using h
  have hr : ((B.lo : ℝ) ≤ 0 ∧ 1 ≤ (B.hi : ℝ)) ∨
      ((A.hi : ℝ) < 0 ∧ (B.lo : ℝ) ≤ 1 ∧ 1 ≤ (B.hi : ℝ)) ∨
      (0 ≤ (A.lo : ℝ) ∧ (B.lo : ℝ) ≤ 0 ∧ 0 ≤ (B.hi : ℝ)) := by exact_mod_cast hq
  rcases hr with h | h | h
  · unfold Contains indicatorLT; split_ifs <;> constructor <;> linarith [h.1,h.2]
  · have hh : x < 0 := hx.2.trans_lt h.1
    simpa [indicatorLT, hh, Contains] using h.2
  · have hh : ¬x < 0 := not_lt.mpr (h.1.trans hx.1)
    simpa [indicatorLT, hh, Contains] using h.2

/-- Discarding a nonnegative weighted component gives a valid lower surrogate. -/
lemma drop_nonnegative {f g w x : ℝ} (hw : 0 ≤ w) (hg : 0 ≤ g)
    (hf : f ≤ x) : f ≤ x + w * g := by nlinarith

/-- Boxwise lower substitutions may be multiplied by nonnegative radial weights. -/
lemma weighted_lower {a b w : ℝ} (h : a ≤ b) (hw : 0 ≤ w) : w * a ≤ w * b :=
  mul_le_mul_of_nonneg_left h hw

lemma clip_lower {l x : ℝ} (_h0 : 0 ≤ l) (h1 : l ≤ 1) (hx : l ≤ x) :
    l ≤ min 1 (max 0 x) := le_min h1 (hx.trans (le_max_right _ _))

end D4Bound.CertificateInterval
