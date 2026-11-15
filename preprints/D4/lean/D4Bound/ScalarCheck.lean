import D4Bound.ScalarData
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# Computable checks for the scalar certificate

Integer polynomial arithmetic on coefficient lists (constant term first) and the Boolean
checks that the kernel runs on the data of `ScalarData.lean`, with their soundness proofs.
-/

namespace D4Bound

/-- Sum of two coefficient lists. -/
def addL : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addL p q

/-- Multiply a polynomial by `A + w`. -/
def mulLin (A : ℤ) (p : List ℤ) : List ℤ := addL (p.map (A * ·)) (0 :: p)

/-- `comp A D P` has the coefficients in `w` of `D ^ deg P * P ((A + w) / D)`. -/
def comp (A D : ℤ) : List ℤ → List ℤ
  | [] => []
  | c :: cs => addL [c * D ^ cs.length] (mulLin A (comp A D cs))

/-- A lower bound for a polynomial on `[0, h]`. -/
def lb (h : ℤ) : List ℤ → ℤ
  | [] => 0
  | c :: cs => c + h * min (lb h cs) 0

/-- The check on one interval `[A/2^k, (A+h)/2^k]`. -/
def leafOK (P : List ℤ) (A k h : ℕ) : Bool := decide (0 < lb h (comp A (2 ^ k) P))

/-- The intervals of `L` tile `[a/2^ka, b/2^kb)` and pass `leafOK`. -/
def chainOK (P : List ℤ) : ℕ → ℕ → List (ℕ × ℕ × ℕ) → ℕ → ℕ → Bool
  | a, ka, [], b, kb => a * 2 ^ kb == b * 2 ^ ka
  | a, ka, (A, k, h) :: rest, b, kb =>
      (a * 2 ^ k == A * 2 ^ ka) && leafOK P A k h && chainOK P (A + h) k rest b kb

/-- Every coefficient of `P (S + w)` is positive. -/
def tailOK (P : List ℤ) (S : ℕ) : Bool :=
  !(comp S 1 P).isEmpty && (comp S 1 P).all (0 < ·)

/-- Coefficient of `s^j` in the transform of `u^k e^{-u}`: `(-1)^j k!/j! C(k+1, k-j)`. -/
def lagCoeff (k j : ℕ) : ℚ :=
  (-1) ^ j * ((k.factorial : ℚ) / j.factorial) * (Nat.choose (k + 1) (k - j))

end D4Bound

/-! ## Soundness -/

namespace D4Bound

/-- Horner evaluation of an integer coefficient list, constant term first. -/
noncomputable def evalZ : List ℤ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * evalZ cs x

lemma evalZ_addL (p q : List ℤ) (x : ℝ) : evalZ (addL p q) x = evalZ p x + evalZ q x := by
  induction p generalizing q with
  | nil => simp [addL, evalZ]
  | cons a p ih =>
    cases q with
    | nil => simp [addL, evalZ]
    | cons b q => simp only [addL, evalZ, ih]; push_cast; ring

lemma evalZ_map_mul (A : ℤ) (p : List ℤ) (x : ℝ) :
    evalZ (p.map (A * ·)) x = A * evalZ p x := by
  induction p with
  | nil => simp [evalZ]
  | cons c p ih => simp only [List.map, evalZ, ih]; push_cast; ring

lemma evalZ_mulLin (A : ℤ) (p : List ℤ) (x : ℝ) :
    evalZ (mulLin A p) x = (A + x) * evalZ p x := by
  simp only [mulLin, evalZ_addL, evalZ_map_mul, evalZ]; push_cast; ring

lemma evalZ_comp (A D : ℤ) (hD : (D : ℝ) ≠ 0) (l : List ℤ) (w : ℝ) :
    (D : ℝ) * evalZ (comp A D l) w = (D : ℝ) ^ l.length * evalZ l ((A + w) / D) := by
  induction l with
  | nil => simp [comp, evalZ]
  | cons c cs ih =>
    have key : evalZ (comp A D (c :: cs)) w =
        (c : ℝ) * (D : ℝ) ^ cs.length + (A + w) * evalZ (comp A D cs) w := by
      simp only [comp, evalZ_addL, evalZ_mulLin, evalZ]; push_cast; ring
    have hDm : (D : ℝ) ^ (cs.length + 1) * ((A + w) / D) = (D : ℝ) ^ cs.length * (A + w) := by
      rw [pow_succ]; field_simp
    rw [key, List.length_cons]
    simp only [evalZ]
    calc (D : ℝ) * ((c : ℝ) * (D : ℝ) ^ cs.length + (A + w) * evalZ (comp A D cs) w)
        = (c : ℝ) * (D : ℝ) ^ (cs.length + 1) + (A + w) * ((D : ℝ) * evalZ (comp A D cs) w) := by
          ring
      _ = (c : ℝ) * (D : ℝ) ^ (cs.length + 1) +
            (A + w) * ((D : ℝ) ^ cs.length * evalZ cs ((A + w) / D)) := by rw [ih]
      _ = (D : ℝ) ^ (cs.length + 1) * ((c : ℝ) + (A + w) / D * evalZ cs ((A + w) / D)) := by
          linear_combination (-evalZ cs ((A + w) / D)) * hDm

lemma lb_le (h : ℤ) (l : List ℤ) {w : ℝ} (hw0 : 0 ≤ w) (hwh : w ≤ h) :
    (lb h l : ℝ) ≤ evalZ l w := by
  induction l with
  | nil => simp [lb, evalZ]
  | cons c cs ih =>
    simp only [lb, evalZ, Int.cast_add, Int.cast_mul]
    have hm1 : ((min (lb h cs) 0 : ℤ) : ℝ) ≤ (lb h cs : ℝ) := by exact_mod_cast min_le_left _ _
    have hm2 : ((min (lb h cs) 0 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast min_le_right _ _
    have e1 : w * ((min (lb h cs) 0 : ℤ) : ℝ) ≤ w * evalZ cs w :=
      mul_le_mul_of_nonneg_left (hm1.trans ih) hw0
    have e2 : (h : ℝ) * ((min (lb h cs) 0 : ℤ) : ℝ) ≤ w * ((min (lb h cs) 0 : ℤ) : ℝ) :=
      mul_le_mul_of_nonpos_right hwh hm2
    linarith

lemma leafOK_sound {P : List ℤ} {A k h : ℕ} (hok : leafOK P A k h = true) (s : ℝ)
    (h1 : (A : ℝ) / 2 ^ k ≤ s) (h2 : s ≤ ((A : ℝ) + h) / 2 ^ k) : 0 < evalZ P s := by
  have hpos : 0 < lb h (comp A (2 ^ k) P) := by simpa [leafOK] using hok
  have hD : (0 : ℝ) < 2 ^ k := by positivity
  set w : ℝ := 2 ^ k * s - A with hw
  have hw0 : 0 ≤ w := by rw [div_le_iff₀ hD] at h1; linarith
  have hwh : w ≤ (h : ℤ) := by rw [le_div_iff₀ hD] at h2; push_cast; linarith
  have hlb := lb_le h (comp A (2 ^ k) P) hw0 hwh
  have hc := evalZ_comp A (2 ^ k) (by positivity) P w
  have hs : ((A : ℤ) + w) / ((2 ^ k : ℤ) : ℝ) = s := by
    push_cast; rw [hw]; field_simp; ring
  rw [hs] at hc
  have hlbR : (0 : ℝ) < (lb h (comp A (2 ^ k) P) : ℝ) := by exact_mod_cast hpos
  have hpow : (0 : ℝ) < ((2 ^ k : ℤ) : ℝ) ^ P.length := by positivity
  have hD' : (0 : ℝ) < ((2 ^ k : ℤ) : ℝ) := by positivity
  have : 0 < ((2 ^ k : ℤ) : ℝ) ^ P.length * evalZ P s := by
    rw [← hc]; exact mul_pos hD' (lt_of_lt_of_le hlbR (by exact_mod_cast hlb))
  exact pos_of_mul_pos_right this hpow.le

/-- `P > 0` on `[lo, hi)`. -/
def PosOn (P : List ℤ) (lo hi : ℝ) : Prop := ∀ s : ℝ, lo ≤ s → s < hi → 0 < evalZ P s

lemma PosOn.trans {P : List ℤ} {a b c : ℝ} (h1 : PosOn P a b) (h2 : PosOn P b c) :
    PosOn P a c := by
  intro s ha hc
  rcases lt_or_ge s b with hb | hb
  · exact h1 s ha hb
  · exact h2 s hb hc

lemma chainOK_sound (P : List ℤ) (L : List (ℕ × ℕ × ℕ)) :
    ∀ (a ka b kb : ℕ), chainOK P a ka L b kb = true →
      PosOn P ((a : ℝ) / 2 ^ ka) ((b : ℝ) / 2 ^ kb) := by
  induction L with
  | nil =>
    intro a ka b kb h s h1 h2
    simp only [chainOK, beq_iff_eq] at h
    have he : (a : ℝ) / 2 ^ ka = (b : ℝ) / 2 ^ kb := by
      rw [div_eq_div_iff (by positivity) (by positivity)]; exact_mod_cast h
    linarith
  | cons leaf rest ih =>
    obtain ⟨A, k, h⟩ := leaf
    intro a ka b kb hok
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hstart, hleaf⟩, hrest⟩ := hok
    have hs : (a : ℝ) / 2 ^ ka = (A : ℝ) / 2 ^ k := by
      rw [div_eq_div_iff (by positivity) (by positivity)]; exact_mod_cast hstart
    have hleafP : PosOn P ((a : ℝ) / 2 ^ ka) (((A + h : ℕ) : ℝ) / 2 ^ k) := by
      intro s h1 h2
      rw [hs] at h1
      exact leafOK_sound hleaf s h1 (by push_cast at h2 ⊢; exact h2.le)
    exact hleafP.trans (ih (A + h) k b kb hrest)

lemma evalZ_pos_of_all_pos (l : List ℤ) (hne : l ≠ []) (hpos : ∀ c ∈ l, 0 < c) {w : ℝ}
    (hw : 0 ≤ w) : 0 < evalZ l w := by
  induction l with
  | nil => exact absurd rfl hne
  | cons c cs ih =>
    simp only [evalZ]
    have hc : (0 : ℝ) < c := by exact_mod_cast hpos c (by simp)
    cases cs with
    | nil => simpa [evalZ] using hc
    | cons d ds =>
      have := ih (List.cons_ne_nil d ds) (fun e he => hpos e (List.mem_cons_of_mem c he))
      positivity

lemma tailOK_sound {P : List ℤ} {S : ℕ} (hok : tailOK P S = true) (s : ℝ) (hs : (S : ℝ) ≤ s) :
    0 < evalZ P s := by
  simp only [tailOK, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, decide_eq_true_eq] at hok
  have hc := evalZ_comp S 1 (by norm_num) P (s - S)
  have hq := evalZ_pos_of_all_pos _ hok.1 hok.2 (w := s - S) (by linarith)
  push_cast at hc
  simp only [one_mul, one_pow, div_one, add_sub_cancel] at hc
  rw [hc] at hq
  exact hq

end D4Bound
