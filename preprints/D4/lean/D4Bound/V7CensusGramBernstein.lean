import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Exact degree-six Bernstein subdivision, with kernel-proved soundness. -/
namespace D4Bound.V7.CensusGram.Bernstein
structure Seven (α : Type) where
  a : α
  b : α
  c : α
  d : α
  e : α
  f : α
  g : α
  deriving Repr, DecidableEq

def Seven.map (f : α → β) (p : Seven α) : Seven β :=
  ⟨f p.a, f p.b, f p.c, f p.d, f p.e, f p.f, f p.g⟩

def eval (p : Seven ℝ) (x : ℝ) : ℝ :=
  1*p.a*x^0*(1-x)^6 + 6*p.b*x^1*(1-x)^5 + 15*p.c*x^2*(1-x)^4 + 20*p.d*x^3*(1-x)^3 + 15*p.e*x^4*(1-x)^2 + 6*p.f*x^5*(1-x)^1 + 1*p.g*x^6*(1-x)^0

def good (p : Seven ℤ) : Bool := decide (0 ≤ p.a ∧ 0 ≤ p.b ∧ 0 ≤ p.c ∧ 0 ≤ p.d ∧ 0 ≤ p.e ∧ 0 ≤ p.f ∧ 0 ≤ p.g)

lemma good_sound (p : Seven ℤ) (h : good p = true) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ eval (p.map Int.cast) x := by
  have hh : 0 ≤ p.a ∧ 0 ≤ p.b ∧ 0 ≤ p.c ∧ 0 ≤ p.d ∧ 0 ≤ p.e ∧ 0 ≤ p.f ∧ 0 ≤ p.g := by simpa [good] using h
  rcases hh with ⟨ha,hb,hc,hd,he,hf,hg⟩
  have hx2 : 0 ≤ 1-x := sub_nonneg.mpr hx1
  unfold eval Seven.map
  positivity

def left (p : Seven ℤ) : Seven ℤ :=
  ⟨64*p.a,
   32*p.a + 32*p.b,
   16*p.a + 32*p.b + 16*p.c,
   8*p.a + 24*p.b + 24*p.c + 8*p.d,
   4*p.a + 16*p.b + 24*p.c + 16*p.d + 4*p.e,
   2*p.a + 10*p.b + 20*p.c + 20*p.d + 10*p.e + 2*p.f,
   1*p.a + 6*p.b + 15*p.c + 20*p.d + 15*p.e + 6*p.f + 1*p.g⟩

lemma eval_left (p : Seven ℤ) (x : ℝ) :
    eval ((left p).map Int.cast) x = 64*eval (p.map Int.cast) (x/2) := by
  simp only [eval, Seven.map, left]
  push_cast
  ring

def right (p : Seven ℤ) : Seven ℤ :=
  ⟨1*p.a + 6*p.b + 15*p.c + 20*p.d + 15*p.e + 6*p.f + 1*p.g,
   2*p.b + 10*p.c + 20*p.d + 20*p.e + 10*p.f + 2*p.g,
   4*p.c + 16*p.d + 24*p.e + 16*p.f + 4*p.g,
   8*p.d + 24*p.e + 24*p.f + 8*p.g,
   16*p.e + 32*p.f + 16*p.g,
   32*p.f + 32*p.g,
   64*p.g⟩

lemma eval_right (p : Seven ℤ) (x : ℝ) :
    eval ((right p).map Int.cast) x = 64*eval (p.map Int.cast) ((x+1)/2) := by
  simp only [eval, Seven.map, right]
  push_cast
  ring

inductive Tree where
  | leaf
  | split (left right : Tree)
  deriving Repr

def check (p : Seven ℤ) : Tree → Bool
  | .leaf => good p
  | .split l r => check (left p) l && check (right p) r

theorem check_sound (tree : Tree) (p : Seven ℤ) (h : check p tree = true)
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ eval (p.map Int.cast) x := by
  induction tree generalizing p x with
  | leaf => exact good_sound p h hx hx1
  | split l r ihl ihr =>
    simp only [check, Bool.and_eq_true] at h
    by_cases hh : x ≤ 1/2
    · have hh := ihl (left p) h.1 (show 0 ≤ 2*x by linarith)
        (show 2*x ≤ 1 by linarith)
      rw [eval_left] at hh
      have he : 2*x/2 = x := by ring
      rw [he] at hh
      linarith
    · have hh := ihr (right p) h.2 (show 0 ≤ 2*x-1 by linarith)
        (show 2*x-1 ≤ 1 by linarith)
      rw [eval_right] at hh
      have he : (2*x-1+1)/2 = x := by ring
      rw [he] at hh
      linarith
end D4Bound.V7.CensusGram.Bernstein
