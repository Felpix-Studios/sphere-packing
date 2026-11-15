import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Exact rational interval certificates

The routines in this module accept rational enclosure witnesses and prove their
soundness over the reals. No external interval-library result is trusted.
This module is infrastructure, not a concrete V7 kernel-box certificate.
-/

namespace D4Bound.CertificateInterval

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

noncomputable def Contains (I : Interval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def subsetOK (A B : Interval) : Bool := decide (B.lo ≤ A.lo ∧ A.hi ≤ B.hi)
def constOK (q : ℚ) (I : Interval) : Bool := decide (I.lo ≤ q ∧ q ≤ I.hi)
def addOK (A B C : Interval) : Bool :=
  decide (C.lo ≤ A.lo + B.lo ∧ A.hi + B.hi ≤ C.hi)
def negOK (A B : Interval) : Bool := decide (B.lo ≤ -A.hi ∧ -A.lo ≤ B.hi)
def mulOK (A B C : Interval) : Bool := decide
  (C.lo ≤ A.lo * B.lo ∧ C.lo ≤ A.lo * B.hi ∧
   C.lo ≤ A.hi * B.lo ∧ C.lo ≤ A.hi * B.hi ∧
   A.lo * B.lo ≤ C.hi ∧ A.lo * B.hi ≤ C.hi ∧
   A.hi * B.lo ≤ C.hi ∧ A.hi * B.hi ≤ C.hi)
def invOK (A B : Interval) : Bool := decide
  ((0 < A.lo ∨ A.hi < 0) ∧ B.lo ≤ A.hi⁻¹ ∧ A.lo⁻¹ ≤ B.hi)
def sqrtOK (A B : Interval) : Bool := decide
  (0 ≤ A.lo ∧ 0 ≤ B.lo ∧ 0 ≤ B.hi ∧ B.lo ^ 2 ≤ A.lo ∧ A.hi ≤ B.hi ^ 2)
def maxOK (A B C : Interval) : Bool := decide
  (C.lo ≤ max A.lo B.lo ∧ max A.hi B.hi ≤ C.hi)
def minOK (A B C : Interval) : Bool := decide
  (C.lo ≤ min A.lo B.lo ∧ min A.hi B.hi ≤ C.hi)

lemma subset_sound {A B : Interval} {x : ℝ}
    (h : subsetOK A B = true) (hx : Contains A x) : Contains B x := by
  have hq : B.lo ≤ A.lo ∧ A.hi ≤ B.hi := by simpa [subsetOK] using h
  have h₀ : (B.lo : ℝ) ≤ A.lo := by exact_mod_cast hq.1
  have h₁ : (A.hi : ℝ) ≤ B.hi := by exact_mod_cast hq.2
  exact ⟨h₀.trans hx.1, hx.2.trans h₁⟩

lemma const_sound {q : ℚ} {I : Interval} (h : constOK q I = true) : Contains I q := by
  have hq : I.lo ≤ q ∧ q ≤ I.hi := by simpa [constOK] using h
  constructor
  · exact_mod_cast hq.1
  · exact_mod_cast hq.2

lemma add_sound {A B C : Interval} {x y : ℝ}
    (h : addOK A B C = true) (hx : Contains A x) (hy : Contains B y) :
    Contains C (x + y) := by
  have hq : C.lo ≤ A.lo + B.lo ∧ A.hi + B.hi ≤ C.hi := by simpa [addOK] using h
  have h₀ : (C.lo : ℝ) ≤ (A.lo : ℝ) + B.lo := by exact_mod_cast hq.1
  have h₁ : (A.hi : ℝ) + B.hi ≤ (C.hi : ℝ) := by exact_mod_cast hq.2
  exact ⟨h₀.trans (add_le_add hx.1 hy.1), (add_le_add hx.2 hy.2).trans h₁⟩

lemma neg_sound {A B : Interval} {x : ℝ}
    (h : negOK A B = true) (hx : Contains A x) : Contains B (-x) := by
  have hq : B.lo ≤ -A.hi ∧ -A.lo ≤ B.hi := by simpa [negOK] using h
  have h₀ : (B.lo : ℝ) ≤ -(A.hi : ℝ) := by exact_mod_cast hq.1
  have h₁ : -(A.lo : ℝ) ≤ (B.hi : ℝ) := by exact_mod_cast hq.2
  exact ⟨h₀.trans (neg_le_neg hx.2), (neg_le_neg hx.1).trans h₁⟩

private lemma bilinear_upper {a b c d x y u : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hac : a * c ≤ u) (had : a * d ≤ u)
    (hbc : b * c ≤ u) (hbd : b * d ≤ u) : x * y ≤ u := by
  rcases le_total 0 y with hy0 | hy0
  · have hxy := mul_le_mul_of_nonneg_right hx.2 hy0
    rcases le_total 0 b with hb0 | hb0
    · exact hxy.trans ((mul_le_mul_of_nonneg_left hy.2 hb0).trans hbd)
    · exact hxy.trans ((mul_le_mul_of_nonpos_left hy.1 hb0).trans hbc)
  · have hxy := mul_le_mul_of_nonpos_right hx.1 hy0
    rcases le_total 0 a with ha0 | ha0
    · exact hxy.trans ((mul_le_mul_of_nonneg_left hy.2 ha0).trans had)
    · exact hxy.trans ((mul_le_mul_of_nonpos_left hy.1 ha0).trans hac)

lemma mul_sound {A B C : Interval} {x y : ℝ}
    (h : mulOK A B C = true) (hx : Contains A x) (hy : Contains B y) :
    Contains C (x * y) := by
  have hq : C.lo ≤ A.lo * B.lo ∧ C.lo ≤ A.lo * B.hi ∧
      C.lo ≤ A.hi * B.lo ∧ C.lo ≤ A.hi * B.hi ∧
      A.lo * B.lo ≤ C.hi ∧ A.lo * B.hi ≤ C.hi ∧
      A.hi * B.lo ≤ C.hi ∧ A.hi * B.hi ≤ C.hi := by simpa [mulOK] using h
  have hr : (C.lo : ℝ) ≤ (A.lo : ℝ) * B.lo ∧ (C.lo : ℝ) ≤ (A.lo : ℝ) * B.hi ∧
      (C.lo : ℝ) ≤ (A.hi : ℝ) * B.lo ∧ (C.lo : ℝ) ≤ (A.hi : ℝ) * B.hi ∧
      (A.lo : ℝ) * B.lo ≤ (C.hi : ℝ) ∧ (A.lo : ℝ) * B.hi ≤ (C.hi : ℝ) ∧
      (A.hi : ℝ) * B.lo ≤ (C.hi : ℝ) ∧ (A.hi : ℝ) * B.hi ≤ (C.hi : ℝ) := by
    exact_mod_cast hq
  rcases hr with ⟨h00,h01,h10,h11,h20,h21,h30,h31⟩
  constructor
  · have hn := bilinear_upper ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩ hy
      (show -(A.hi : ℝ) * B.lo ≤ -(C.lo : ℝ) by nlinarith)
      (show -(A.hi : ℝ) * B.hi ≤ -(C.lo : ℝ) by nlinarith)
      (show -(A.lo : ℝ) * B.lo ≤ -(C.lo : ℝ) by nlinarith)
      (show -(A.lo : ℝ) * B.hi ≤ -(C.lo : ℝ) by nlinarith)
    nlinarith
  · exact bilinear_upper hx hy h20 h21 h30 h31

lemma inv_sound {A B : Interval} {x : ℝ}
    (h : invOK A B = true) (hx : Contains A x) : Contains B x⁻¹ := by
  have hq : (0 < A.lo ∨ A.hi < 0) ∧ B.lo ≤ A.hi⁻¹ ∧ A.lo⁻¹ ≤ B.hi := by
    simpa [invOK] using h
  have hlo : (B.lo : ℝ) ≤ (A.hi : ℝ)⁻¹ := by exact_mod_cast hq.2.1
  have hhi : (A.lo : ℝ)⁻¹ ≤ (B.hi : ℝ) := by exact_mod_cast hq.2.2
  rcases hq.1 with hp | hn
  · have hp' : (0 : ℝ) < A.lo := by exact_mod_cast hp
    have hx' : 0 < x := hp'.trans_le hx.1
    exact ⟨hlo.trans ((inv_le_inv₀ (hx'.trans_le hx.2) hx').mpr hx.2),
      ((inv_le_inv₀ hx' hp').mpr hx.1).trans hhi⟩
  · have hn' : (A.hi : ℝ) < 0 := by exact_mod_cast hn
    have hx' : x < 0 := hx.2.trans_lt hn'
    exact ⟨hlo.trans ((inv_le_inv_of_neg hn' hx').mpr hx.2),
      ((inv_le_inv_of_neg hx' (hx.1.trans_lt hx')).mpr hx.1).trans hhi⟩

lemma sqrt_sound {A B : Interval} {x : ℝ}
    (h : sqrtOK A B = true) (hx : Contains A x) : Contains B (Real.sqrt x) := by
  have hq : 0 ≤ A.lo ∧ 0 ≤ B.lo ∧ 0 ≤ B.hi ∧ B.lo ^ 2 ≤ A.lo ∧ A.hi ≤ B.hi ^ 2 := by
    simpa [sqrtOK] using h
  have hr : (0 : ℝ) ≤ A.lo ∧ (0 : ℝ) ≤ B.lo ∧ (0 : ℝ) ≤ B.hi ∧
      (B.lo : ℝ) ^ 2 ≤ (A.lo : ℝ) ∧ (A.hi : ℝ) ≤ (B.hi : ℝ) ^ 2 := by exact_mod_cast hq
  have hx0 := hr.1.trans hx.1
  have hs := Real.sq_sqrt hx0
  have hn := Real.sqrt_nonneg x
  constructor <;> nlinarith [hx.1,hx.2,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2]

lemma max_sound {A B C : Interval} {x y : ℝ}
    (h : maxOK A B C = true) (hx : Contains A x) (hy : Contains B y) :
    Contains C (max x y) := by
  have hq : C.lo ≤ max A.lo B.lo ∧ max A.hi B.hi ≤ C.hi := by simpa [maxOK] using h
  have hr : (C.lo : ℝ) ≤ max (A.lo : ℝ) B.lo ∧ max (A.hi : ℝ) B.hi ≤ (C.hi : ℝ) := by
    exact_mod_cast hq
  exact ⟨hr.1.trans (max_le_max hx.1 hy.1), (max_le_max hx.2 hy.2).trans hr.2⟩

lemma min_sound {A B C : Interval} {x y : ℝ}
    (h : minOK A B C = true) (hx : Contains A x) (hy : Contains B y) :
    Contains C (min x y) := by
  have hq : C.lo ≤ min A.lo B.lo ∧ min A.hi B.hi ≤ C.hi := by simpa [minOK] using h
  have hr : (C.lo : ℝ) ≤ min (A.lo : ℝ) B.lo ∧ min (A.hi : ℝ) B.hi ≤ (C.hi : ℝ) := by
    exact_mod_cast hq
  exact ⟨hr.1.trans (min_le_min hx.1 hy.1), (min_le_min hx.2 hy.2).trans hr.2⟩

end D4Bound.CertificateInterval
