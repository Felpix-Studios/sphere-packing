import D4Bound.V7ExpressionSemantics
import D4Bound.V7ExpressionProgram
import D4Bound.V7ExpressionBranches

/-! Coordinate targets for actual-kernel certificates. These theorems contain
no sign assumption from an external checker. Closed radial selectors remain
explicit hypotheses at the interface. -/
namespace D4Bound.V7Expression
open Expr
open scoped RealInnerProductSpace

def pairExpr (p q : ℕ) : Expr := pairE p q (.var 0) (.var 1) (.var 2)

def pairSlackExpr (p q : ℕ) (lambda a : ℚ) : Expr :=
  -pairExpr p q - .rat lambda * ((.var 2)^4 - (.rat a)^2 * (.var 2)^2)

/-- Pair at a triangle vertex, in side-length coordinates r,s,d. -/
def trianglePairExpr (p q : ℕ) (r s d : Expr) : Expr :=
  pairE p q r s ((r^2+s^2-d^2)/(2*r*s))

def triangleSumExpr (p q k : ℕ) : Expr :=
  trianglePairExpr p q (.var 0) (.var 1) (.var 2) +
  trianglePairExpr p k (.var 0) (.var 2) (.var 1) +
  trianglePairExpr q k (.var 1) (.var 2) (.var 0)

noncomputable section

theorem eval_pairExpr (xs : ℕ → ℝ) (p q : ℕ)
    (hp : V7.radialPiece (xs 0) = p) (hq : V7.radialPiece (xs 1) = q) :
    eval xs (pairExpr p q) = V7.pair (xs 0) (xs 1) (xs 2) :=
  eval_pairE xs p q (.var 0) (.var 1) (.var 2) hp hq

theorem eval_pairSlackExpr (xs : ℕ → ℝ) (p q : ℕ) (lambda a : ℚ)
    (hp : V7.radialPiece (xs 0) = p) (hq : V7.radialPiece (xs 1) = q) :
    eval xs (pairSlackExpr p q lambda a) =
      -V7.pair (xs 0) (xs 1) (xs 2) -
        (lambda : ℝ)*((xs 2)^4-(a : ℝ)^2*(xs 2)^2) := by
  simp only [pairSlackExpr, eval_sub, eval_neg, eval_mul, eval_rat, eval_pow,
    eval_var, eval_pairExpr xs p q hp hq]

theorem eval_trianglePairExpr (xs : ℕ → ℝ) (p q : ℕ) (r s d : Expr)
    (hp : V7.radialPiece (eval xs r) = p) (hq : V7.radialPiece (eval xs s) = q) :
    eval xs (trianglePairExpr p q r s d) =
      V7.pair (eval xs r) (eval xs s)
        (((eval xs r)^2+(eval xs s)^2-(eval xs d)^2)/(2*eval xs r*eval xs s)) := by
  rw [trianglePairExpr, eval_pairE xs p q _ _ _ hp hq]
  simp only [eval_div, eval_sub, eval_add, eval_pow, eval_mul, eval_num2]

/-- Interface for a formally reflected kernel-box slack certificate. -/
theorem pairSlack_nonneg_of_program {nvar : ℕ} {inputs : ℕ → CertificateInterval.Interval}
    {rows : List CertificateInterval.Row} {xs : ℕ → ℝ} (p q : ℕ) (lambda a : ℚ)
    (hp : V7.radialPiece (xs 0) = p) (hq : V7.radialPiece (xs 1) = q)
    (he : reflect rows = pairSlackExpr p q lambda a)
    (hc : CertificateInterval.nonnegOK nvar inputs rows = true)
    (hin : CertificateInterval.InDomain inputs xs) :
    0 ≤ -V7.pair (xs 0) (xs 1) (xs 2) -
      (lambda : ℝ)*((xs 2)^4-(a : ℝ)^2*(xs 2)^2) := by
  rw [← eval_pairSlackExpr xs p q lambda a hp hq]
  exact nonneg_of_program he hc hin

/-- Branch-specialized programs have the same actual-kernel conclusion. -/
theorem pairSlack_nonneg_of_specialized_program
    {nvar : ℕ} {inputs : ℕ → CertificateInterval.Interval}
    {rows : List CertificateInterval.Row} {xs : ℕ → ℝ} (p q : ℕ) (lambda a : ℚ)
    (hp : V7.radialPiece (xs 0) = p) (hq : V7.radialPiece (xs 1) = q)
    (g : Guards) (hg : GuardsSound xs g)
    (he : reflect rows = specialize g (pairSlackExpr p q lambda a))
    (hc : CertificateInterval.nonnegOK nvar inputs rows = true)
    (hin : CertificateInterval.InDomain inputs xs) :
    0 ≤ -V7.pair (xs 0) (xs 1) (xs 2) -
      (lambda : ℝ)*((xs 2)^4-(a : ℝ)^2*(xs 2)^2) := by
  have h := nonneg_of_program he hc hin
  rw [eval_specialize xs g hg, eval_pairSlackExpr xs p q lambda a hp hq] at h
  exact h

/-- Supported nonorigin kernel equals the physical radial pair. -/
theorem kernel_eq_pair {x y : E4} (hx1 : 1 ≤ ‖x‖) (hy1 : 1 ≤ ‖y‖)
    (hxR : ‖x‖ ≤ 7/4) (hyR : ‖y‖ ≤ 7/4) :
    V7.kernel x y = V7.pair ‖x‖ ‖y‖ (⟪x,y⟫/(‖x‖*‖y‖)) := by
  have hx0 : x ≠ 0 := by intro h; subst x; norm_num at hx1
  have hy0 : y ≠ 0 := by intro h; subst y; norm_num at hy1
  simp only [V7.kernel, not_lt.mpr hxR, not_lt.mpr hyR, or_self, if_false,
    hx0, hy0, hx1, hy1, and_self, if_true]

#print axioms eval_pairE
#print axioms nonneg_of_program
#print axioms eval_specialize
#print axioms intervalGuard_sound
#print axioms pairSlack_nonneg_of_program
#print axioms pairSlack_nonneg_of_specialized_program
#print axioms kernel_eq_pair
end
end D4Bound.V7Expression
