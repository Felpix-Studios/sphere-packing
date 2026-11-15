import D4Bound.V7Expression
import D4Bound.CertificateIntervalProgram

/-! Syntactic reflection of the checked interval program. The bridge accepts
an equality of expressions, never an external equality-checker status. -/
namespace D4Bound.V7Expression
open Expr

/-- Backwards-register expression corresponding to one interval-program op. -/
def reflectOp (es : List Expr) : CertificateInterval.Op → Expr
  | .const q => .rat q
  | .var i => .var i
  | .add i j => .add (es.getD i 0) (es.getD j 0)
  | .neg i => .neg (es.getD i 0)
  | .mul i j => .mul (es.getD i 0) (es.getD j 0)
  | .inv i => .inv (es.getD i 0)
  | .sqrt i => .sqrt (es.getD i 0)
  | .exp _ i => .exp (es.getD i 0)
  | .max i j => .max (es.getD i 0) (es.getD j 0)
  | .min i j => .min (es.getD i 0) (es.getD j 0)

def reflectFrom : List Expr → List CertificateInterval.Row → List Expr
  | es, [] => es
  | es, row :: rest => reflectFrom (reflectOp es row.op :: es) rest

def reflect (rows : List CertificateInterval.Row) : Expr := (reflectFrom [] rows).getD 0 0

noncomputable section
lemma eval_getD (xs : ℕ → ℝ) (es : List Expr) (i : ℕ) :
    Expr.eval xs (es.getD i 0) = (es.map (Expr.eval xs)).getD i 0 := by
  induction es generalizing i with
  | nil => change ((0 : ℚ) : ℝ) = 0; exact Rat.cast_zero
  | cons e es ih => cases i with
    | zero => rfl
    | succ i => exact ih i

lemma eval_reflectOp (xs : ℕ → ℝ) (es : List Expr) (op : CertificateInterval.Op) :
    Expr.eval xs (reflectOp es op) = CertificateInterval.evalOp xs (es.map (Expr.eval xs)) op := by
  cases op <;> simp only [reflectOp, Expr.eval, CertificateInterval.evalOp, eval_getD]

lemma eval_reflectFrom (xs : ℕ → ℝ) (es : List Expr) (rows : List CertificateInterval.Row) :
    (reflectFrom es rows).map (Expr.eval xs) =
      CertificateInterval.evalFrom xs (es.map (Expr.eval xs)) rows := by
  induction rows generalizing es with
  | nil => rfl
  | cons row rest ih =>
    simp only [reflectFrom, ih, List.map_cons, eval_reflectOp, CertificateInterval.evalFrom]

/-- Exact semantic equality for every program, including empty or invalid programs. -/
theorem eval_reflect (xs : ℕ → ℝ) (rows : List CertificateInterval.Row) :
    Expr.eval xs (reflect rows) = CertificateInterval.eval xs rows := by
  simp only [reflect, eval_getD, eval_reflectFrom, List.map_nil, CertificateInterval.eval]

/-- A checked program proves a sign of the expression it actually represents. -/
theorem nonneg_of_program {nvar : ℕ} {inputs : ℕ → CertificateInterval.Interval}
    {rows : List CertificateInterval.Row} {xs : ℕ → ℝ} {e : Expr}
    (hexpr : reflect rows = e)
    (hcheck : CertificateInterval.nonnegOK nvar inputs rows = true)
    (hin : CertificateInterval.InDomain inputs xs) : 0 ≤ Expr.eval xs e := by
  rw [← hexpr, eval_reflect]
  exact CertificateInterval.nonneg_sound hcheck hin

end
end D4Bound.V7Expression
