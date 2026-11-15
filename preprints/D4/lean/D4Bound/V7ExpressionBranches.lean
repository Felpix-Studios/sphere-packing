import D4Bound.V7Expression

/-! Exact branch specialization. A chosen branch requires a proof of its actual
real comparison; unknown comparisons remain literal. This is suitable for
radial-cell specialization before interval or polynomial certificate replay. -/
namespace D4Bound.V7Expression
open Expr

inductive Test where | le | lt | eq
  deriving Repr, DecidableEq

noncomputable def Test.holds (test : Test) (x y : ℝ) : Prop :=
  match test with | .le => x ≤ y | .lt => x < y | .eq => x = y

abbrev Guards := Test → Expr → Expr → Option Bool

noncomputable def GuardsSound (xs : ℕ → ℝ) (g : Guards) : Prop :=
  ∀ test a b v, g test a b = some v →
    (Test.holds test (eval xs a) (eval xs b) ↔ v = true)

/-- Specialize only comparisons decided by the supplied sound guard table. -/
def specialize (g : Guards) : Expr → Expr
  | .rat q => .rat q
  | .var i => .var i
  | .add a b => .add (specialize g a) (specialize g b)
  | .neg a => .neg (specialize g a)
  | .mul a b => .mul (specialize g a) (specialize g b)
  | .inv a => .inv (specialize g a)
  | .sqrt a => .sqrt (specialize g a)
  | .exp a => .exp (specialize g a)
  | .max a b => .max (specialize g a) (specialize g b)
  | .min a b => .min (specialize g a) (specialize g b)
  | .ifLE a b c d => match g .le a b with
    | some true => specialize g c
    | some false => specialize g d
    | none => .ifLE (specialize g a) (specialize g b) (specialize g c) (specialize g d)
  | .ifLT a b c d => match g .lt a b with
    | some true => specialize g c
    | some false => specialize g d
    | none => .ifLT (specialize g a) (specialize g b) (specialize g c) (specialize g d)
  | .ifEQ a b c d => match g .eq a b with
    | some true => specialize g c
    | some false => specialize g d
    | none => .ifEQ (specialize g a) (specialize g b) (specialize g c) (specialize g d)

/-- Rational separation decides a comparison only when its interval endpoints
force that result. The strictness differs between LE and LT. -/
def intervalGuard (test : Test) (A B : CertificateInterval.Interval) : Option Bool :=
  match test with
  | .le => if A.hi ≤ B.lo then some true else if B.hi < A.lo then some false else none
  | .lt => if A.hi < B.lo then some true else if B.hi ≤ A.lo then some false else none
  | .eq => if A.lo = A.hi ∧ B.lo = B.hi ∧ A.lo = B.lo then some true
    else if A.hi < B.lo ∨ B.hi < A.lo then some false else none

noncomputable section
/-- Exact endpoint tests justify the chosen branch, including singleton equality. -/
theorem intervalGuard_sound (test : Test) (A B : CertificateInterval.Interval)
    (x y : ℝ) (hA : CertificateInterval.Contains A x) (hB : CertificateInterval.Contains B y)
    (v : Bool) (h : intervalGuard test A B = some v) :
    Test.holds test x y ↔ v = true := by
  rcases hA with ⟨ha0,ha1⟩
  rcases hB with ⟨hb0,hb1⟩
  cases test <;> simp only [intervalGuard] at h
  · split_ifs at h with ht hf
    · have hr : (A.hi : ℝ) ≤ (B.lo : ℝ) := by exact_mod_cast ht
      cases Option.some.inj h
      simp only [Test.holds, iff_true, eq_self]
      exact ha1.trans (hr.trans hb0)
    · have hr : (B.hi : ℝ) < (A.lo : ℝ) := by exact_mod_cast hf
      cases Option.some.inj h
      simp only [Test.holds, Bool.false_eq_true, iff_false, not_le]
      exact hb1.trans_lt (hr.trans_le ha0)
  · split_ifs at h with ht hf
    · have hr : (A.hi : ℝ) < (B.lo : ℝ) := by exact_mod_cast ht
      cases Option.some.inj h
      simp only [Test.holds, iff_true, eq_self]
      exact ha1.trans_lt (hr.trans_le hb0)
    · have hr : (B.hi : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast hf
      cases Option.some.inj h
      simp only [Test.holds, Bool.false_eq_true, iff_false, not_lt]
      exact hb1.trans (hr.trans ha0)
  · split_ifs at h with ht hf
    · have hr : (A.lo : ℝ) = A.hi ∧ (B.lo : ℝ) = B.hi ∧ (A.lo : ℝ) = B.lo := by exact_mod_cast ht
      cases Option.some.inj h
      simp only [Test.holds, iff_true, eq_self]
      rcases hr with ⟨h0,h1,h2⟩
      linarith
    · have hr : (A.hi : ℝ) < B.lo ∨ (B.hi : ℝ) < A.lo := by exact_mod_cast hf
      cases Option.some.inj h
      simp only [Test.holds, Bool.false_eq_true, iff_false]
      rcases hr with hr | hr <;> linarith

/-- Branch specialization preserves all real semantics, including endpoints. -/
theorem eval_specialize (xs : ℕ → ℝ) (g : Guards) (hg : GuardsSound xs g) (e : Expr) :
    eval xs (specialize g e) = eval xs e := by
  induction e with
  | rat q => rfl
  | var i => rfl
  | add a b ha hb => simp only [specialize, eval, ha, hb]
  | neg a ha => simp only [specialize, eval, ha]
  | mul a b ha hb => simp only [specialize, eval, ha, hb]
  | inv a ha => simp only [specialize, eval, ha]
  | sqrt a ha => simp only [specialize, eval, ha]
  | exp a ha => simp only [specialize, eval, ha]
  | max a b ha hb => simp only [specialize, eval, ha, hb]
  | min a b ha hb => simp only [specialize, eval, ha, hb]
  | ifLE a b c d ha hb hc hd =>
    cases h : g .le a b with
    | none => simp only [specialize, h, eval, ha, hb, hc, hd]
    | some v =>
      have hv := hg .le a b v h
      cases v <;> simp_all [specialize, eval, Test.holds]
  | ifLT a b c d ha hb hc hd =>
    cases h : g .lt a b with
    | none => simp only [specialize, h, eval, ha, hb, hc, hd]
    | some v =>
      have hv := hg .lt a b v h
      cases v <;> simp_all [specialize, eval, Test.holds]
  | ifEQ a b c d ha hb hc hd =>
    cases h : g .eq a b with
    | none => simp only [specialize, h, eval, ha, hb, hc, hd]
    | some v =>
      have hv := hg .eq a b v h
      cases v <;> simp_all [specialize, eval, Test.holds]

end
end D4Bound.V7Expression
