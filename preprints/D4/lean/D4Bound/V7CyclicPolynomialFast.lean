import D4Bound.V7CyclicPolynomialBasic

/-! Linear merging of sparse coefficient lists. The fuel fallback preserves
evaluation even for malformed or unordered input; no ordering axiom is used. -/
namespace D4Bound.V7.CyclicPoly

def merge : ℕ → Poly → Poly → Poly
  | 0,p,q => p++q
  | _+1,[],q => q
  | _+1,p,[] => p
  | n+1,a::p,b::q =>
    if a.1 = b.1 then
      if a.2+b.2 = 0 then merge n p q else (a.1,a.2+b.2)::merge n p q
    else if before a.1 b.1 then a::merge n p (b::q)
    else b::merge n (a::p) q

def fastAdd (p q : Poly) : Poly := merge (p.length+q.length) p q
def fastMul (p q : Poly) : Poly := p.foldr (fun a z => fastAdd (mulTerm a q) z) []
def fastPower (p : Poly) : ℕ → Poly
  | 0 => constant 1
  | n+1 => fastMul (fastPower p n) p
def fastSum (ps : List Poly) : Poly := ps.foldr fastAdd []

theorem eval_merge (n : ℕ) (p q : Poly) (r s d : ℝ) :
    eval (merge n p q) r s d = eval p r s d+eval q r s d := by
  induction n generalizing p q with
  | zero => simp [merge,eval,List.map_append,List.sum_append]
  | succ n ih =>
    cases p with
    | nil => simp [merge]
    | cons a p =>
      cases q with
      | nil => simp [merge]
      | cons b q =>
        simp only [merge]
        split_ifs with hab hz hb
        · have hterm : termEval a r s d+termEval b r s d = 0 := by
            simp only [termEval]
            rw [hab,← add_mul,← Rat.cast_add,hz,Rat.cast_zero,zero_mul]
          simp only [ih,eval_cons]
          linarith
        · simp only [eval_cons,ih,termEval,Rat.cast_add]
          rw [hab]
          ring
        · simp only [eval_cons,ih]
          ring
        · simp only [eval_cons,ih]
          ring

theorem eval_fastAdd (p q : Poly) (r s d : ℝ) :
    eval (fastAdd p q) r s d = eval p r s d+eval q r s d :=
  eval_merge _ _ _ _ _ _

theorem eval_fastMul (p q : Poly) (r s d : ℝ) :
    eval (fastMul p q) r s d = eval p r s d*eval q r s d := by
  induction p with
  | nil => simp [fastMul]
  | cons a p ih =>
    simp only [fastMul,List.foldr_cons,eval_fastAdd,eval_mulTerm,eval_cons] at *
    rw [ih]
    ring

theorem eval_fastPower (p : Poly) (n : ℕ) (r s d : ℝ) :
    eval (fastPower p n) r s d = eval p r s d^n := by
  induction n with
  | zero => simp [fastPower]
  | succ n ih => rw [fastPower,eval_fastMul,ih,pow_succ]

theorem eval_fastSum (ps : List Poly) (r s d : ℝ) :
    eval (fastSum ps) r s d = (ps.map fun p => eval p r s d).sum := by
  induction ps with
  | nil => simp [fastSum]
  | cons p ps ih =>
    simp only [fastSum,List.foldr_cons,eval_fastAdd,List.map_cons,List.sum_cons] at *
    rw [ih]

end D4Bound.V7.CyclicPoly

#print axioms D4Bound.V7.CyclicPoly.eval_fastMul
