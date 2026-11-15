import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Executable dense polynomials with real semantics

Polynomials are coefficient lists, constant term first. A coefficient type comes with
executable operations (`Alg`) and an evaluation into `ℝ` that respects them (`Model`).
`polyAlg` lifts the operations to lists, so `ℚ`, `List ℚ`, `List (List ℚ)`, ... are all
covered by the same lemmas. Everything here uses only the three standard axioms; the
functions are meant to be run by `native_decide` in separate check modules.
-/

namespace D4Bound.KBN

/-- Executable coefficient operations. -/
structure Alg (α : Type) where
  zero : α
  add : α → α → α
  mul : α → α → α
  smul : ℚ → α → α
  ofQ : ℚ → α

/-- `ev` respects the operations of `A`. -/
structure Model {α : Type} (A : Alg α) (ev : α → ℝ) : Prop where
  zero : ev A.zero = 0
  add : ∀ a b, ev (A.add a b) = ev a + ev b
  mul : ∀ a b, ev (A.mul a b) = ev a * ev b
  smul : ∀ q a, ev (A.smul q a) = q * ev a
  ofQ : ∀ q, ev (A.ofQ q) = q

def qAlg : Alg ℚ := ⟨0, (· + ·), (· * ·), (· * ·), id⟩

theorem qModel : Model qAlg (fun q : ℚ => (q : ℝ)) where
  zero := by simp [qAlg]
  add := by intro a b; simp [qAlg]
  mul := by intro a b; simp [qAlg]
  smul := by intro a b; simp [qAlg]
  ofQ := by intro q; simp [qAlg]

section Generic
variable {α : Type} (A : Alg α)

def padd : List α → List α → List α
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => A.add a b :: padd p q

def psmul (q : ℚ) (p : List α) : List α := p.map (A.smul q)

def pmul : List α → List α → List α
  | [], _ => []
  | a :: p, q => padd A (q.map (A.mul a)) (A.zero :: pmul p q)

def polyAlg : Alg (List α) where
  zero := []
  add := padd A
  mul := pmul A
  smul := psmul A
  ofQ q := [A.ofQ q]

/-- Taylor shift: `pshift c p` represents `x ↦ p (c + x)`. -/
def pshift (c : ℚ) : List α → List α
  | [] => []
  | a :: p =>
    let q := pshift c p
    padd A [a] (padd A (psmul A c q) (A.zero :: q))

/-- Horner evaluation inside another algebra. -/
def horner {β : Type} (B : Alg β) (emb : α → β) (x : β) : List α → β
  | [] => B.zero
  | a :: p => B.add (emb a) (B.mul x (horner B emb x p))

end Generic

/-- Horner evaluation in `ℝ`. -/
noncomputable def peval {α : Type} (ev : α → ℝ) (x : ℝ) : List α → ℝ
  | [] => 0
  | a :: p => ev a + x * peval ev x p

section Semantics
variable {α : Type} {A : Alg α} {ev : α → ℝ}

@[simp] theorem peval_nil (x : ℝ) : peval ev x [] = 0 := rfl
@[simp] theorem peval_cons (x : ℝ) (a : α) (p : List α) :
    peval ev x (a :: p) = ev a + x * peval ev x p := rfl

theorem peval_padd (hM : Model A ev) (x : ℝ) :
    ∀ p q : List α, peval ev x (padd A p q) = peval ev x p + peval ev x q
  | [], q => by simp [padd]
  | a :: p, [] => by simp [padd]
  | a :: p, b :: q => by
    simp only [padd, peval_cons, hM.add, peval_padd hM x p q]; ring

theorem peval_map_mul (hM : Model A ev) (x : ℝ) (a : α) :
    ∀ q : List α, peval ev x (q.map (A.mul a)) = ev a * peval ev x q
  | [] => by simp
  | b :: q => by
    simp only [List.map_cons, peval_cons, hM.mul, peval_map_mul hM x a q]; ring

theorem peval_psmul (hM : Model A ev) (x : ℝ) (c : ℚ) :
    ∀ q : List α, peval ev x (psmul A c q) = c * peval ev x q
  | [] => by simp [psmul]
  | b :: q => by
    have := peval_psmul hM x c q
    simp only [psmul, List.map_cons, peval_cons, hM.smul] at this ⊢
    rw [this]; ring

theorem peval_pmul (hM : Model A ev) (x : ℝ) :
    ∀ p q : List α, peval ev x (pmul A p q) = peval ev x p * peval ev x q
  | [], q => by simp [pmul]
  | a :: p, q => by
    simp only [pmul, peval_padd hM, peval_map_mul hM, peval_cons, hM.zero,
      peval_pmul hM x p q]
    ring

theorem polyModel (hM : Model A ev) (x : ℝ) : Model (polyAlg A) (peval ev x) where
  zero := rfl
  add := peval_padd hM x
  mul := peval_pmul hM x
  smul := peval_psmul hM x
  ofQ q := by simp [polyAlg, hM.ofQ]

theorem peval_pshift (hM : Model A ev) (c : ℚ) (x : ℝ) :
    ∀ p : List α, peval ev x (pshift A c p) = peval ev ((c : ℝ) + x) p
  | [] => by simp [pshift]
  | a :: p => by
    simp only [pshift, peval_padd hM, peval_psmul hM, peval_cons, peval_nil, hM.zero,
      peval_pshift hM c x p]
    ring

theorem peval_map {β : Type} {ev' : β → ℝ} (f : α → β) (h : ∀ a, ev' (f a) = ev a)
    (x : ℝ) : ∀ p : List α, peval ev' x (p.map f) = peval ev x p
  | [] => by simp
  | a :: p => by simp [h, peval_map f h x p]

theorem eval_horner {β : Type} {B : Alg β} {evB : β → ℝ} (hB : Model B evB)
    (emb : α → β) (hemb : ∀ a, evB (emb a) = ev a) (x : β) :
    ∀ p : List α, evB (horner B emb x p) = peval ev (evB x) p
  | [] => by simp [horner, hB.zero]
  | a :: p => by simp [horner, hB.add, hB.mul, hemb, eval_horner hB emb hemb x p]

end Semantics

/-! ## Sums and powers -/

section Ops
variable {α : Type} (A : Alg α)

def psum (L : List (List α)) : List α := L.foldr (padd A) []

def ppow (p : List α) : ℕ → List α
  | 0 => [A.ofQ 1]
  | n + 1 => pmul A p (ppow p n)

variable {A} {ev : α → ℝ}

theorem peval_psum (hM : Model A ev) (x : ℝ) :
    ∀ L : List (List α), peval ev x (psum A L) = (L.map (peval ev x)).sum
  | [] => by simp [psum]
  | p :: L => by
    have := peval_psum hM x L
    simp only [psum, List.foldr_cons] at this ⊢
    rw [peval_padd hM, this]; simp

theorem peval_ppow (hM : Model A ev) (x : ℝ) (p : List α) :
    ∀ n : ℕ, peval ev x (ppow A p n) = peval ev x p ^ n
  | 0 => by simp [ppow, hM.ofQ]
  | n + 1 => by rw [ppow, peval_pmul hM, peval_ppow hM x p n]; ring

end Ops

/-! ## Lower and absolute bounds on a symmetric box -/

section Bounds
variable {α : Type}

/-- `Σ abs(aₖ) hᵏ`. -/
def absP (abs : α → ℚ) (h : ℚ) : List α → ℚ
  | [] => 0
  | a :: p => abs a + h * absP abs h p

/-- Lower bound of `Σ_{j} aⱼ x^{k+j}` given `|x| ≤ h`, with `e` the parity of `k` and
`hk = hᵏ`: even powers keep the sign of a lower bound, odd powers use the absolute bound. -/
def lowFrom (low abs : α → ℚ) (h : ℚ) : Bool → ℚ → List α → ℚ
  | _, _, [] => 0
  | e, hk, a :: p =>
    (if e then min 0 (low a) * hk else -(abs a * hk)) + lowFrom low abs h (!e) (hk * h) p

def lowP (low abs : α → ℚ) (h : ℚ) : List α → ℚ
  | [] => 0
  | a :: p => low a + lowFrom low abs h false h p

variable {ev : α → ℝ} {low abs : α → ℚ} {h : ℚ} {x : ℝ}

theorem absP_sound (habs : ∀ a, |ev a| ≤ abs a) (hx : |x| ≤ h) :
    ∀ p : List α, |peval ev x p| ≤ absP abs h p
  | [] => by simp [absP]
  | a :: p => by
    have ih := absP_sound habs hx p
    simp only [peval_cons, absP]; push_cast
    have hh : (0 : ℝ) ≤ h := le_trans (abs_nonneg x) hx
    calc |ev a + x * peval ev x p| ≤ |ev a| + |x| * |peval ev x p| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ abs a + h * absP abs h p := by
          gcongr
          · exact habs a

theorem lowFrom_sound (hlow : ∀ a, (low a : ℝ) ≤ ev a) (habs : ∀ a, |ev a| ≤ abs a)
    (hx : |x| ≤ h) : ∀ (p : List α) (k : ℕ),
    (lowFrom low abs h (decide (Even k)) (h ^ k) p : ℝ) ≤ x ^ k * peval ev x p
  | [], k => by simp [lowFrom]
  | a :: p, k => by
    have hh : (0 : ℝ) ≤ h := le_trans (abs_nonneg x) hx
    have ih := lowFrom_sound hlow habs hx p (k + 1)
    have hpar : (!decide (Even k)) = decide (Even (k + 1)) := by
      by_cases he : Even k <;> simp [he, Nat.even_add_one]
    have hxk : |x ^ k| ≤ (h : ℝ) ^ k := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg x) hx k
    simp only [lowFrom, hpar, ← pow_succ]
    push_cast
    have hterm : ((if decide (Even k) then min 0 (low a) * h ^ k else -(abs a * h ^ k) : ℚ) : ℝ)
        ≤ x ^ k * ev a := by
      by_cases he : Even k
      · simp only [he, decide_true, if_true]
        push_cast
        have hxk0 : 0 ≤ x ^ k := he.pow_nonneg x
        have hxkh : x ^ k ≤ (h : ℝ) ^ k := le_trans (le_abs_self _) hxk
        have hm : (min 0 (low a : ℝ)) ≤ 0 := min_le_left _ _
        have hm2 : (min 0 (low a : ℝ)) ≤ ev a := le_trans (min_le_right _ _) (hlow a)
        nlinarith
      · simp only [he, decide_false, Bool.false_eq_true, if_false]
        push_cast
        have h1 : |x ^ k * ev a| ≤ (h : ℝ) ^ k * abs a := by
          rw [abs_mul]; exact mul_le_mul hxk (habs a) (abs_nonneg _) (by positivity)
        have := neg_abs_le (x ^ k * ev a)
        linarith
    calc _ ≤ x ^ k * ev a + x ^ (k + 1) * peval ev x p := add_le_add hterm ih
      _ = x ^ k * peval ev x (a :: p) := by simp only [peval_cons]; ring

theorem lowP_sound (hlow : ∀ a, (low a : ℝ) ≤ ev a) (habs : ∀ a, |ev a| ≤ abs a)
    (hx : |x| ≤ h) : ∀ p : List α, (lowP low abs h p : ℝ) ≤ peval ev x p
  | [] => by simp [lowP]
  | a :: p => by
    have := lowFrom_sound hlow habs hx p 1
    simp only [pow_one, show decide (Even 1) = false by decide] at this
    simp only [lowP, peval_cons]; push_cast
    linarith [hlow a]

end Bounds

/-! ## Concrete levels: one, two and three variables -/

abbrev P1 := List ℚ
abbrev P2 := List P1
abbrev P3 := List P2

def A1 : Alg P1 := polyAlg qAlg
def A2 : Alg P2 := polyAlg A1
def A3 : Alg P3 := polyAlg A2

noncomputable def E1 (p : P1) (x : ℝ) : ℝ := peval (fun q : ℚ => (q : ℝ)) x p
noncomputable def E2 (p : P2) (y z : ℝ) : ℝ := peval (fun c => E1 c z) y p
noncomputable def E3 (p : P3) (x y z : ℝ) : ℝ := peval (fun c => E2 c y z) x p

theorem M1 (z : ℝ) : Model A1 (fun p => E1 p z) := polyModel qModel z
theorem M2 (y z : ℝ) : Model A2 (fun p => E2 p y z) := polyModel (M1 z) y
theorem M3 (x y z : ℝ) : Model A3 (fun p => E3 p x y z) := polyModel (M2 y z) x

/-- Shift all three variables to a centre. -/
def shift3 (cu cv ct : ℚ) (p : P3) : P3 :=
  (pshift A2 cu p).map fun q => (pshift A1 cv q).map fun r => pshift qAlg ct r

theorem E1_pshift (c : ℚ) (p : P1) (z : ℝ) : E1 (pshift qAlg c p) z = E1 p (c + z) := by
  unfold E1; exact peval_pshift qModel c z p

theorem E2_shift (cv ct : ℚ) (q : P2) (y z : ℝ) :
    E2 ((pshift A1 cv q).map fun r => pshift qAlg ct r) y z = E2 q (cv + y) (ct + z) := by
  unfold E2
  have h1 := peval_map (ev' := fun c : P1 => E1 c z) (ev := fun c : P1 => E1 c (ct + z))
    (fun r => pshift qAlg ct r) (fun c => E1_pshift ct c z) y (pshift A1 cv q)
  rw [h1]
  exact peval_pshift (M1 (ct + z)) cv y q

theorem E3_shift3 (cu cv ct : ℚ) (p : P3) (x y z : ℝ) :
    E3 (shift3 cu cv ct p) x y z = E3 p (cu + x) (cv + y) (ct + z) := by
  unfold shift3 E3
  have h1 := peval_map (ev' := fun c : P2 => E2 c y z) (ev := fun c : P2 => E2 c (cv + y) (ct + z))
    (fun q => (pshift A1 cv q).map fun r => pshift qAlg ct r) (fun c => E2_shift cv ct c y z) x
    (pshift A2 cu p)
  rw [h1]
  exact peval_pshift (M2 (cv + y) (ct + z)) cu x p

/-- Lower bound of a three-variable polynomial on `|x| ≤ hu`, `|y| ≤ hv`, `|z| ≤ ht`. -/
def low1 (ht : ℚ) : P1 → ℚ := lowP id (fun q => |q|) ht
def abs1 (ht : ℚ) : P1 → ℚ := absP (fun q => |q|) ht
def low2 (hv ht : ℚ) : P2 → ℚ := lowP (low1 ht) (abs1 ht) hv
def abs2 (hv ht : ℚ) : P2 → ℚ := absP (abs1 ht) hv
def low3 (hu hv ht : ℚ) : P3 → ℚ := lowP (low2 hv ht) (abs2 hv ht) hu

theorem bounds1 {ht : ℚ} {z : ℝ} (hz : |z| ≤ ht) (p : P1) :
    (low1 ht p : ℝ) ≤ E1 p z ∧ |E1 p z| ≤ abs1 ht p := by
  constructor
  · exact lowP_sound (ev := fun q : ℚ => (q : ℝ)) (fun a => le_rfl)
      (fun a => by simp [Rat.cast_abs]) hz p
  · exact absP_sound (ev := fun q : ℚ => (q : ℝ)) (fun a => by simp [Rat.cast_abs]) hz p

theorem bounds2 {hv ht : ℚ} {y z : ℝ} (hy : |y| ≤ hv) (hz : |z| ≤ ht) (p : P2) :
    (low2 hv ht p : ℝ) ≤ E2 p y z ∧ |E2 p y z| ≤ abs2 hv ht p :=
  ⟨lowP_sound (ev := fun c => E1 c z) (fun a => (bounds1 hz a).1) (fun a => (bounds1 hz a).2) hy p,
   absP_sound (ev := fun c => E1 c z) (fun a => (bounds1 hz a).2) hy p⟩

theorem low3_sound {hu hv ht : ℚ} {x y z : ℝ} (hx : |x| ≤ hu) (hy : |y| ≤ hv)
    (hz : |z| ≤ ht) (p : P3) : (low3 hu hv ht p : ℝ) ≤ E3 p x y z :=
  lowP_sound (ev := fun c => E2 c y z) (fun a => (bounds2 hy hz a).1)
    (fun a => (bounds2 hy hz a).2) hx p

/-- Lifts of one-variable polynomials into the three variables `(u, v, t)`. -/
def liftU (p : P1) : P3 := p.map fun c => [[c]]
def liftV (p : P1) : P3 := [p.map fun c => [c]]
def liftT (p : P1) : P3 := [[p]]
def const3 (q : ℚ) : P3 := [[[q]]]

@[simp] theorem E1_singleton (q : ℚ) (z : ℝ) : E1 [q] z = q := by simp [E1]
@[simp] theorem E2_singleton (p : P1) (y z : ℝ) : E2 [p] y z = E1 p z := by simp [E2]
@[simp] theorem E3_singleton (p : P2) (x y z : ℝ) : E3 [p] x y z = E2 p y z := by simp [E3]

theorem E3_liftU (p : P1) (x y z : ℝ) : E3 (liftU p) x y z = E1 p x := by
  unfold liftU E3 E1
  exact peval_map _ (fun c => by simp [E2, E1]) x p

theorem E3_liftV (p : P1) (x y z : ℝ) : E3 (liftV p) x y z = E1 p y := by
  unfold liftV
  rw [E3_singleton]
  unfold E2 E1
  exact peval_map _ (fun c => by simp [E1]) y p

theorem E3_liftT (p : P1) (x y z : ℝ) : E3 (liftT p) x y z = E1 p z := by
  simp [liftT]

theorem E3_const3 (q : ℚ) (x y z : ℝ) : E3 (const3 q) x y z = q := by
  simp [const3]

theorem E3_add (p q : P3) (x y z : ℝ) : E3 (A3.add p q) x y z = E3 p x y z + E3 q x y z :=
  (M3 x y z).add p q
theorem E3_mul (p q : P3) (x y z : ℝ) : E3 (A3.mul p q) x y z = E3 p x y z * E3 q x y z :=
  (M3 x y z).mul p q
theorem E3_smul (c : ℚ) (p : P3) (x y z : ℝ) : E3 (A3.smul c p) x y z = c * E3 p x y z :=
  (M3 x y z).smul c p
theorem E3_zero (x y z : ℝ) : E3 A3.zero x y z = 0 := (M3 x y z).zero
theorem E3_psum (L : List P3) (x y z : ℝ) :
    E3 (psum A2 L) x y z = (L.map fun p => E3 p x y z).sum := by
  unfold E3; exact peval_psum (M2 y z) x L

theorem E1_add (p q : P1) (x : ℝ) : E1 (A1.add p q) x = E1 p x + E1 q x := (M1 x).add p q
theorem E1_mul (p q : P1) (x : ℝ) : E1 (A1.mul p q) x = E1 p x * E1 q x := (M1 x).mul p q
theorem E1_smul (c : ℚ) (p : P1) (x : ℝ) : E1 (A1.smul c p) x = c * E1 p x := (M1 x).smul c p
theorem E1_psum (L : List P1) (x : ℝ) : E1 (psum qAlg L) x = (L.map fun p => E1 p x).sum := by
  unfold E1; exact peval_psum qModel x L
theorem E1_ppow (p : P1) (n : ℕ) (x : ℝ) : E1 (ppow qAlg p n) x = E1 p x ^ n := by
  unfold E1; exact peval_ppow qModel x p n

/-- One-variable lower bound and shift. -/
theorem low1_shift_sound {c h : ℚ} {x : ℝ} (hx : |x - c| ≤ h) (p : P1) :
    (low1 h (pshift qAlg c p) : ℝ) ≤ E1 p x := by
  have := (bounds1 hx (pshift qAlg c p)).1
  unfold E1 at this ⊢
  rwa [peval_pshift qModel, add_sub_cancel] at this

end D4Bound.KBN
