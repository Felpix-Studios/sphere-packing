import Mathlib.Tactic

/-! Executable sparse rational polynomials in the three side coordinates.
All arithmetic is interpreted by a proved real evaluation map. -/
namespace D4Bound.V7.CyclicPoly

abbrev Exponent := ℕ × ℕ × ℕ
abbrev Term := Exponent × ℚ
abbrev Poly := List Term

def before (a b : Exponent) : Bool :=
  decide (a.1 < b.1 ∨ a.1 = b.1 ∧
    (a.2.1 < b.2.1 ∨ a.2.1 = b.2.1 ∧ a.2.2 < b.2.2))

def insert (t : Term) : Poly → Poly
  | [] => if t.2 = 0 then [] else [t]
  | u :: p =>
    if t.1 = u.1 then
      if t.2 + u.2 = 0 then p else (t.1,t.2+u.2) :: p
    else if before t.1 u.1 then
      if t.2 = 0 then u :: p else t :: u :: p
    else u :: insert t p

def add (p q : Poly) : Poly := p.foldr insert q
def scale (a : ℚ) (p : Poly) : Poly :=
  p.foldr (fun t q => insert (t.1,a*t.2) q) []
def termMul (a b : Term) : Term :=
  ((a.1.1+b.1.1,a.1.2.1+b.1.2.1,a.1.2.2+b.1.2.2),a.2*b.2)
def mulTerm (a : Term) (p : Poly) : Poly := p.map (termMul a)
def mul (p q : Poly) : Poly := p.foldr (fun a z => add (mulTerm a q) z) []
def constant (a : ℚ) : Poly := if a = 0 then [] else [((0,0,0),a)]
def coordinate (i : Fin 3) : Poly :=
  [((if i=0 then 1 else 0,if i=1 then 1 else 0,if i=2 then 1 else 0),1)]
def power (p : Poly) : ℕ → Poly
  | 0 => constant 1
  | n+1 => mul (power p n) p
def sum (ps : List Poly) : Poly := ps.foldr add []

noncomputable def monomial (a : Exponent) (r s d : ℝ) : ℝ :=
  r^a.1*s^a.2.1*d^a.2.2
noncomputable def termEval (a : Term) (r s d : ℝ) : ℝ :=
  (a.2 : ℝ)*monomial a.1 r s d
noncomputable def eval (p : Poly) (r s d : ℝ) : ℝ :=
  (p.map fun t => termEval t r s d).sum

@[simp] theorem eval_nil (r s d : ℝ) : eval [] r s d = 0 := rfl
@[simp] theorem eval_cons (a : Term) (p : Poly) (r s d : ℝ) :
    eval (a::p) r s d = termEval a r s d+eval p r s d := rfl

theorem eval_insert (a : Term) (p : Poly) (r s d : ℝ) :
    eval (insert a p) r s d = termEval a r s d+eval p r s d := by
  induction p with
  | nil =>
    simp only [insert]
    split_ifs with h
    · simp [termEval,h]
    · simp
  | cons b p ih =>
    simp only [insert]
    split_ifs with hab hz hb hz
    · have hterm : termEval a r s d+termEval b r s d = 0 := by
        simp only [termEval]
        rw [hab,← add_mul,← Rat.cast_add,hz,Rat.cast_zero,zero_mul]
      simp only [eval_cons]
      linarith
    · simp only [eval_cons,termEval, Rat.cast_add]
      rw [hab]
      ring
    · simp [termEval,hz]
    · simp
    · simp only [eval_cons,ih]
      ring

theorem eval_add (p q : Poly) (r s d : ℝ) :
    eval (add p q) r s d = eval p r s d+eval q r s d := by
  induction p with
  | nil => simp [add]
  | cons a p ih =>
    simp only [add,List.foldr_cons,eval_insert,eval_cons] at *
    rw [ih]
    ring

theorem eval_scale (a : ℚ) (p : Poly) (r s d : ℝ) :
    eval (scale a p) r s d = (a : ℝ)*eval p r s d := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
    simp only [scale,List.foldr_cons,eval_insert,eval_cons] at *
    rw [ih]
    simp only [termEval,Rat.cast_mul]
    ring

theorem termEval_mul (a b : Term) (r s d : ℝ) :
    termEval (termMul a b) r s d = termEval a r s d*termEval b r s d := by
  simp only [termEval,termMul,monomial,Rat.cast_mul,pow_add]
  ring

theorem eval_mulTerm (a : Term) (p : Poly) (r s d : ℝ) :
    eval (mulTerm a p) r s d = termEval a r s d*eval p r s d := by
  induction p with
  | nil => simp [mulTerm]
  | cons b p ih =>
    simp only [mulTerm,List.map_cons,eval_cons] at *
    rw [termEval_mul,ih]
    ring

theorem eval_mul (p q : Poly) (r s d : ℝ) :
    eval (mul p q) r s d = eval p r s d*eval q r s d := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    simp only [mul,List.foldr_cons,eval_add,eval_mulTerm,eval_cons] at *
    rw [ih]
    ring

@[simp] theorem eval_constant (a : ℚ) (r s d : ℝ) :
    eval (constant a) r s d = (a : ℝ) := by
  unfold constant
  split_ifs with h <;> simp [eval,termEval,monomial,h]

@[simp] theorem eval_coordinate0 (r s d : ℝ) : eval (coordinate 0) r s d = r := by
  norm_num [coordinate,eval,termEval,monomial,Fin.ext_iff]
@[simp] theorem eval_coordinate1 (r s d : ℝ) : eval (coordinate 1) r s d = s := by
  norm_num [coordinate,eval,termEval,monomial,Fin.ext_iff]
@[simp] theorem eval_coordinate2 (r s d : ℝ) : eval (coordinate 2) r s d = d := by
  norm_num [coordinate,eval,termEval,monomial,Fin.ext_iff]

theorem eval_power (p : Poly) (n : ℕ) (r s d : ℝ) :
    eval (power p n) r s d = eval p r s d^n := by
  induction n with
  | zero => simp [power]
  | succ n ih => rw [power,eval_mul,ih,pow_succ]

theorem eval_sum (ps : List Poly) (r s d : ℝ) :
    eval (sum ps) r s d = (ps.map fun p => eval p r s d).sum := by
  induction ps with
  | nil => simp [sum]
  | cons p ps ih =>
    simp only [sum,List.foldr_cons,eval_add,List.map_cons,List.sum_cons] at *
    rw [ih]

end D4Bound.V7.CyclicPoly

#print axioms D4Bound.V7.CyclicPoly.eval_mul
