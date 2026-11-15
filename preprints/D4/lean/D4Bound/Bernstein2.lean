import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! A small exact checker for sign conditions on four bicubic Bernstein polynomials.
The coefficients are integers, and each half-split multiplies all values by eight.
All soundness lemmas are proved in Lean; no external arithmetic result is assumed. -/
namespace D4Bound.LatitudeCheck

structure Four (α : Type) where
  a : α
  b : α
  c : α
  d : α
  deriving Repr, DecidableEq

def Four.map (f : α → β) (v : Four α) : Four β := ⟨f v.a, f v.b, f v.c, f v.d⟩
def Four.zip (f : α → β → γ) (v : Four α) (w : Four β) : Four γ :=
  ⟨f v.a w.a, f v.b w.b, f v.c w.c, f v.d w.d⟩

def E (v : Four ℝ) (x : ℝ) : ℝ :=
  v.a * (1-x)^3 + 3*v.b*x*(1-x)^2 + 3*v.c*x^2*(1-x) + v.d*x^3

lemma E_ge {v : Four ℝ} {x L : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (ha : L ≤ v.a) (hb : L ≤ v.b) (hc : L ≤ v.c) (hd : L ≤ v.d) : L ≤ E v x := by
  have h0 : 0 ≤ (v.a-L)*(1-x)^3 := mul_nonneg (by linarith) (pow_nonneg (by linarith) _)
  have h1 : 0 ≤ 3*(v.b-L)*x*(1-x)^2 := by positivity
  have h2 : 0 ≤ 3*(v.c-L)*x^2*(1-x) := by positivity
  have h3 : 0 ≤ (v.d-L)*x^3 := by positivity
  unfold E
  nlinarith

lemma E_le {v : Four ℝ} {x L : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (ha : v.a ≤ L) (hb : v.b ≤ L) (hc : v.c ≤ L) (hd : v.d ≤ L) : E v x ≤ L := by
  have h0 : 0 ≤ (L-v.a)*(1-x)^3 := mul_nonneg (by linarith) (pow_nonneg (by linarith) _)
  have h1 : 0 ≤ 3*(L-v.b)*x*(1-x)^2 := by positivity
  have h2 : 0 ≤ 3*(L-v.c)*x^2*(1-x) := by positivity
  have h3 : 0 ≤ (L-v.d)*x^3 := by positivity
  unfold E
  nlinarith

abbrev Poly := Four (Four ℤ)
noncomputable def ev (p : Poly) (x y : ℝ) : ℝ := E (p.map fun v => E (v.map Int.cast) y) x

def rowGe (v : Four ℤ) (n : ℤ) : Bool := decide (n ≤ v.a ∧ n ≤ v.b ∧ n ≤ v.c ∧ n ≤ v.d)
def rowLe (v : Four ℤ) (n : ℤ) : Bool := decide (v.a ≤ n ∧ v.b ≤ n ∧ v.c ≤ n ∧ v.d ≤ n)
def ge (p : Poly) (n : ℤ) : Bool := rowGe p.a n && rowGe p.b n && rowGe p.c n && rowGe p.d n
def le (p : Poly) (n : ℤ) : Bool := rowLe p.a n && rowLe p.b n && rowLe p.c n && rowLe p.d n

lemma rowGe_sound {v : Four ℤ} {n : ℤ} (h : rowGe v n = true) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : (n : ℝ) ≤ E (v.map Int.cast) x := by
  have h' : n ≤ v.a ∧ n ≤ v.b ∧ n ≤ v.c ∧ n ≤ v.d := by simpa [rowGe] using h
  apply E_ge hx hx1 <;> simp only [Four.map]
  · exact_mod_cast h'.1
  · exact_mod_cast h'.2.1
  · exact_mod_cast h'.2.2.1
  · exact_mod_cast h'.2.2.2

lemma rowLe_sound {v : Four ℤ} {n : ℤ} (h : rowLe v n = true) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : E (v.map Int.cast) x ≤ (n : ℝ) := by
  have h' : v.a ≤ n ∧ v.b ≤ n ∧ v.c ≤ n ∧ v.d ≤ n := by simpa [rowLe] using h
  apply E_le hx hx1 <;> simp only [Four.map]
  · exact_mod_cast h'.1
  · exact_mod_cast h'.2.1
  · exact_mod_cast h'.2.2.1
  · exact_mod_cast h'.2.2.2

lemma ge_sound {p : Poly} {n : ℤ} (h : ge p n = true) {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) : (n : ℝ) ≤ ev p x y := by
  have h' : rowGe p.a n = true ∧ rowGe p.b n = true ∧ rowGe p.c n = true ∧ rowGe p.d n = true := by
    simpa [ge, Bool.and_eq_true, and_assoc] using h
  apply E_ge hx hx1 <;> simp only [Four.map]
  · exact rowGe_sound h'.1 hy hy1
  · exact rowGe_sound h'.2.1 hy hy1
  · exact rowGe_sound h'.2.2.1 hy hy1
  · exact rowGe_sound h'.2.2.2 hy hy1

lemma le_sound {p : Poly} {n : ℤ} (h : le p n = true) {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) : ev p x y ≤ (n : ℝ) := by
  have h' : rowLe p.a n = true ∧ rowLe p.b n = true ∧ rowLe p.c n = true ∧ rowLe p.d n = true := by
    simpa [le, Bool.and_eq_true, and_assoc] using h
  apply E_le hx hx1 <;> simp only [Four.map]
  · exact rowLe_sound h'.1 hy hy1
  · exact rowLe_sound h'.2.1 hy hy1
  · exact rowLe_sound h'.2.2.1 hy hy1
  · exact rowLe_sound h'.2.2.2 hy hy1

def add (v w : Four ℤ) : Four ℤ := Four.zip (·+·) v w
def smul (n : ℤ) (v : Four ℤ) : Four ℤ := v.map (n*·)
def splitL (p : Poly) : Poly :=
  ⟨smul 8 p.a, smul 4 (add p.a p.b), smul 2 (add (add p.a (smul 2 p.b)) p.c),
    add (add (add p.a (smul 3 p.b)) (smul 3 p.c)) p.d⟩
def splitR (p : Poly) : Poly :=
  ⟨add (add (add p.a (smul 3 p.b)) (smul 3 p.c)) p.d,
    smul 2 (add (add p.b (smul 2 p.c)) p.d), smul 4 (add p.c p.d), smul 8 p.d⟩
def transpose (p : Poly) : Poly :=
  ⟨⟨p.a.a,p.b.a,p.c.a,p.d.a⟩,⟨p.a.b,p.b.b,p.c.b,p.d.b⟩,
   ⟨p.a.c,p.b.c,p.c.c,p.d.c⟩,⟨p.a.d,p.b.d,p.c.d,p.d.d⟩⟩
def splitYL (p : Poly) : Poly := transpose (splitL (transpose p))
def splitYR (p : Poly) : Poly := transpose (splitR (transpose p))

lemma ev_splitL (p : Poly) (x y : ℝ) : ev (splitL p) x y = 8 * ev p (x/2) y := by
  simp only [ev, E, Four.map, splitL, add, smul, Four.zip]
  push_cast
  ring
lemma ev_splitR (p : Poly) (x y : ℝ) : ev (splitR p) x y = 8 * ev p ((x+1)/2) y := by
  simp only [ev, E, Four.map, splitR, add, smul, Four.zip]
  push_cast
  ring
lemma ev_transpose (p : Poly) (x y : ℝ) : ev (transpose p) x y = ev p y x := by
  simp only [ev, E, Four.map, transpose]
  ring
lemma ev_splitYL (p : Poly) (x y : ℝ) : ev (splitYL p) x y = 8 * ev p x (y/2) := by
  rw [splitYL, ev_transpose, ev_splitL, ev_transpose]
lemma ev_splitYR (p : Poly) (x y : ℝ) : ev (splitYR p) x y = 8 * ev p x ((y+1)/2) := by
  rw [splitYR, ev_transpose, ev_splitR, ev_transpose]

structure Bundle where
  P : Poly
  V : Poly
  H : Poly
  D : Poly
  deriving Repr

def Bundle.map (f : Poly → Poly) (p : Bundle) : Bundle := ⟨f p.P, f p.V, f p.H, f p.D⟩
def Good (p : Bundle) (x y : ℝ) : Prop :=
  ev p.D x y < 0 ∨
  (0 ≤ ev p.P x y ∧ ev p.V x y ≤ 0) ∨
  (0 ≤ ev p.P x y ∧ 0 ≤ ev p.H x y) ∨
  (ev p.V x y ≤ 0 ∧ ev p.H x y ≤ 0)

def leafOK (p : Bundle) : Bool :=
  le p.D (-1) || (ge p.P 0 && le p.V 0) || (ge p.P 0 && ge p.H 0) || (le p.V 0 && le p.H 0)

lemma leafOK_sound (p : Bundle) (h : leafOK p = true) {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) : Good p x y := by
  simp only [leafOK, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ((h | ⟨hP,hV⟩) | ⟨hP,hH⟩) | ⟨hV,hH⟩
  · left; have := le_sound h hx hx1 hy hy1; norm_num at this; linarith
  · exact Or.inr (Or.inl ⟨by simpa using ge_sound hP hx hx1 hy hy1, by simpa using le_sound hV hx hx1 hy hy1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by simpa using ge_sound hP hx hx1 hy hy1, by simpa using ge_sound hH hx hx1 hy hy1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by simpa using le_sound hV hx hx1 hy hy1, by simpa using le_sound hH hx hx1 hy hy1⟩))

lemma good_of_scale {p q : Bundle} {x y u v : ℝ}
    (hP : ev q.P u v = 8 * ev p.P x y) (hV : ev q.V u v = 8 * ev p.V x y)
    (hH : ev q.H u v = 8 * ev p.H x y) (hD : ev q.D u v = 8 * ev p.D x y)
    (h : Good q u v) : Good p x y := by
  unfold Good at h ⊢
  rw [hP,hV,hH,hD] at h
  rcases h with h | ⟨hP,hV⟩ | ⟨hP,hH⟩ | ⟨hV,hH⟩
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl ⟨by linarith,by linarith⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by linarith,by linarith⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by linarith,by linarith⟩))

inductive Tree where
  | leaf
  | x (left right : Tree)
  | y (left right : Tree)
  deriving Repr

def check (p : Bundle) : Tree → Bool
  | .leaf => leafOK p
  | .x l r => check (p.map splitL) l && check (p.map splitR) r
  | .y l r => check (p.map splitYL) l && check (p.map splitYR) r

lemma check_sound (tree : Tree) (p : Bundle) (h : check p tree = true) {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) : Good p x y := by
  induction tree generalizing p x y with
  | leaf => exact leafOK_sound p h hx hx1 hy hy1
  | x l r ihl ihr =>
    simp only [check, Bool.and_eq_true] at h
    by_cases hh : x ≤ 1/2
    · have hg := ihl (p.map splitL) h.1 (show 0 ≤ 2*x by linarith) (show 2*x ≤ 1 by linarith) hy hy1
      apply good_of_scale (q:=p.map splitL) (u:=2*x) (v:=y) (h:=hg)
      all_goals simp only [Bundle.map, ev_splitL]; congr 2 <;> ring
    · have hg := ihr (p.map splitR) h.2 (show 0 ≤ 2*x-1 by linarith) (show 2*x-1 ≤ 1 by linarith) hy hy1
      apply good_of_scale (q:=p.map splitR) (u:=2*x-1) (v:=y) (h:=hg)
      all_goals simp only [Bundle.map, ev_splitR]; congr 2 <;> ring
  | y l r ihl ihr =>
    simp only [check, Bool.and_eq_true] at h
    by_cases hh : y ≤ 1/2
    · have hg := ihl (p.map splitYL) h.1 hx hx1 (show 0 ≤ 2*y by linarith) (show 2*y ≤ 1 by linarith)
      apply good_of_scale (q:=p.map splitYL) (u:=x) (v:=2*y) (h:=hg)
      all_goals simp only [Bundle.map, ev_splitYL]; congr 2 <;> ring
    · have hg := ihr (p.map splitYR) h.2 hx hx1 (show 0 ≤ 2*y-1 by linarith) (show 2*y-1 ≤ 1 by linarith)
      apply good_of_scale (q:=p.map splitYR) (u:=x) (v:=2*y-1) (h:=hg)
      all_goals simp only [Bundle.map, ev_splitYR]; congr 2 <;> ring

end D4Bound.LatitudeCheck
