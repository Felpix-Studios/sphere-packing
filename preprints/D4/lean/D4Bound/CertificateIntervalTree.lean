import D4Bound.CertificateIntervalProgram

/-! Kernel-checkable finite split covers for one exact straight-line expression. -/
namespace D4Bound.CertificateInterval

noncomputable def evalOpsFrom (xs : ℕ → ℝ) : List ℝ → List Op → List ℝ
  | vs, [] => vs
  | vs, op :: ops => evalOpsFrom xs (evalOp xs vs op :: vs) ops

noncomputable def evalOps (xs : ℕ → ℝ) (ops : List Op) : ℝ :=
  (evalOpsFrom xs [] ops).getD 0 0

lemma evalFrom_eq_ops (xs : ℕ → ℝ) (vs : List ℝ) (rows : List Row) :
    evalFrom xs vs rows = evalOpsFrom xs vs (rows.map Row.op) := by
  induction rows generalizing vs with
  | nil => rfl
  | cons row rest ih => exact ih _

lemma checked_ops_nonneg {nvar : ℕ} {inputs : ℕ → Interval} {rows : List Row}
    {ops : List Op} {xs : ℕ → ℝ}
    (hops : rows.map Row.op = ops) (h : nonnegOK nvar inputs rows = true)
    (hin : InDomain inputs xs) : 0 ≤ evalOps xs ops := by
  have hn := nonneg_sound h hin
  simpa only [eval, evalFrom_eq_ops, hops, evalOps] using hn

inductive Tree where
  | leaf (rows : List Row)
  | split (coordinate : ℕ) (cut : ℚ) (left right : Tree)
  deriving Repr

def leftBox (b : ℕ → Interval) (d : ℕ) (c : ℚ) : ℕ → Interval :=
  Function.update b d ⟨(b d).lo,c⟩

def rightBox (b : ℕ → Interval) (d : ℕ) (c : ℚ) : ℕ → Interval :=
  Function.update b d ⟨c,(b d).hi⟩

def checkTree (nvar : ℕ) (ops : List Op) : (ℕ → Interval) → Tree → Bool
  | b, .leaf rows => (rows.map Row.op == ops) && nonnegOK nvar b rows
  | b, .split d c left right =>
      decide (d < nvar ∧ (b d).lo ≤ c ∧ c ≤ (b d).hi) &&
      checkTree nvar ops (leftBox b d c) left && checkTree nvar ops (rightBox b d c) right

lemma in_left {b : ℕ → Interval} {d : ℕ} {c : ℚ} {xs : ℕ → ℝ}
    (h : InDomain b xs) (hc : xs d ≤ (c : ℝ)) : InDomain (leftBox b d c) xs := by
  intro i
  by_cases hi : i = d
  · subst i
    simpa [leftBox, Contains] using And.intro (h d).1 hc
  · simpa [leftBox, hi] using h i

lemma in_right {b : ℕ → Interval} {d : ℕ} {c : ℚ} {xs : ℕ → ℝ}
    (h : InDomain b xs) (hc : (c : ℝ) ≤ xs d) : InDomain (rightBox b d c) xs := by
  intro i
  by_cases hi : i = d
  · subst i
    simpa [rightBox, Contains] using And.intro hc (h d).2
  · simpa [rightBox, hi] using h i

/-- Every accepted leaf is checked, and both closed sides cover each parent box. -/
theorem checkTree_sound {nvar : ℕ} {ops : List Op} (tree : Tree)
    {b : ℕ → Interval} {xs : ℕ → ℝ}
    (h : checkTree nvar ops b tree = true) (hin : InDomain b xs) :
    0 ≤ evalOps xs ops := by
  induction tree generalizing b with
  | leaf rows =>
    simp only [checkTree, Bool.and_eq_true, beq_iff_eq] at h
    exact checked_ops_nonneg h.1 h.2 hin
  | split d c left right ihl ihr =>
    simp only [checkTree, Bool.and_eq_true] at h
    rcases le_total (xs d) (c : ℝ) with hl | hr
    · exact ihl h.1.2 (in_left hin hl)
    · exact ihr h.2 (in_right hin hr)

end D4Bound.CertificateInterval
