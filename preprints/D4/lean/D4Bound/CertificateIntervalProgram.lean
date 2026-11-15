import D4Bound.CertificateIntervalExp

/-!
# Checked straight-line interval programs

References count backwards from the most recently computed value. A Boolean
check enforces that every referenced register already exists. The soundness
proof covers the actual real evaluation of the program; the exported interval
witnesses are only data and cannot assert a real inequality without checking.
-/
namespace D4Bound.CertificateInterval

inductive Op where
  | const (q : ℚ)
  | var (i : ℕ)
  | add (i j : ℕ)
  | neg (i : ℕ)
  | mul (i j : ℕ)
  | inv (i : ℕ)
  | sqrt (i : ℕ)
  | exp (degree i : ℕ)
  | max (i j : ℕ)
  | min (i j : ℕ)
  deriving Repr, DecidableEq

structure Row where
  op : Op
  bound : Interval
  deriving Repr, DecidableEq

def zeroInterval : Interval := ⟨0,0⟩

def getI (bs : List Interval) (i : ℕ) : Interval := bs.getD i zeroInterval

noncomputable def evalOp (xs : ℕ → ℝ) (vs : List ℝ) : Op → ℝ
  | .const q => q
  | .var i => xs i
  | .add i j => vs.getD i 0 + vs.getD j 0
  | .neg i => -vs.getD i 0
  | .mul i j => vs.getD i 0 * vs.getD j 0
  | .inv i => (vs.getD i 0)⁻¹
  | .sqrt i => Real.sqrt (vs.getD i 0)
  | .exp _ i => Real.exp (vs.getD i 0)
  | .max i j => max (vs.getD i 0) (vs.getD j 0)
  | .min i j => min (vs.getD i 0) (vs.getD j 0)

def validOp (nvar nreg : ℕ) : Op → Bool
  | .const _ => true
  | .var i => decide (i < nvar)
  | .add i j | .mul i j | .max i j | .min i j => decide (i < nreg ∧ j < nreg)
  | .neg i | .inv i | .sqrt i | .exp _ i => decide (i < nreg)

def checkOp (inputs : ℕ → Interval) (regs : List Interval) (out : Interval) : Op → Bool
  | .const q => constOK q out
  | .var i => subsetOK (inputs i) out
  | .add i j => addOK (getI regs i) (getI regs j) out
  | .neg i => negOK (getI regs i) out
  | .mul i j => mulOK (getI regs i) (getI regs j) out
  | .inv i => invOK (getI regs i) out
  | .sqrt i => sqrtOK (getI regs i) out
  | .exp degree i => expOK degree (getI regs i) out
  | .max i j => maxOK (getI regs i) (getI regs j) out
  | .min i j => minOK (getI regs i) (getI regs j) out

noncomputable def Encloses (bs : List Interval) (vs : List ℝ) : Prop :=
  ∀ i, Contains (getI bs i) (vs.getD i 0)

noncomputable def InDomain (inputs : ℕ → Interval) (xs : ℕ → ℝ) : Prop :=
  ∀ i, Contains (inputs i) (xs i)

lemma checkOp_sound {inputs : ℕ → Interval} {regs : List Interval} {xs : ℕ → ℝ} {vs : List ℝ}
    {out : Interval} {op : Op}
    (h : checkOp inputs regs out op = true)
    (hin : InDomain inputs xs) (hreg : Encloses regs vs) :
    Contains out (evalOp xs vs op) := by
  cases op with
  | const q => exact const_sound h
  | var i => exact subset_sound h (hin i)
  | add i j => exact add_sound h (hreg i) (hreg j)
  | neg i => exact neg_sound h (hreg i)
  | mul i j => exact mul_sound h (hreg i) (hreg j)
  | inv i => exact inv_sound h (hreg i)
  | sqrt i => exact sqrt_sound h (hreg i)
  | exp degree i => exact exp_sound h (hreg i)
  | max i j => exact max_sound h (hreg i) (hreg j)
  | min i j => exact min_sound h (hreg i) (hreg j)

lemma encloses_nil : Encloses [] [] := by
  intro i
  simp [getI, zeroInterval, Contains]

lemma encloses_cons {bs : List Interval} {vs : List ℝ} {b : Interval} {v : ℝ}
    (hb : Contains b v) (h : Encloses bs vs) : Encloses (b :: bs) (v :: vs) := by
  intro i
  cases i with
  | zero => simpa [getI] using hb
  | succ i => simpa [getI] using h i

def checkFrom (nvar : ℕ) (inputs : ℕ → Interval) : List Interval → List Row → Bool
  | _, [] => true
  | regs, row :: rest =>
      validOp nvar regs.length row.op &&
      checkOp inputs regs row.bound row.op && checkFrom nvar inputs (row.bound :: regs) rest

noncomputable def evalFrom (xs : ℕ → ℝ) : List ℝ → List Row → List ℝ
  | vs, [] => vs
  | vs, row :: rest => evalFrom xs (evalOp xs vs row.op :: vs) rest

def boundsFrom : List Interval → List Row → List Interval
  | bs, [] => bs
  | bs, row :: rest => boundsFrom (row.bound :: bs) rest

lemma checkFrom_sound {nvar : ℕ} {inputs : ℕ → Interval} {regs : List Interval} {xs : ℕ → ℝ} {vs : List ℝ}
    (rows : List Row) (hin : InDomain inputs xs) (hr : Encloses regs vs)
    (h : checkFrom nvar inputs regs rows = true) :
    Encloses (boundsFrom regs rows) (evalFrom xs vs rows) := by
  induction rows generalizing regs vs with
  | nil => exact hr
  | cons row rest ih =>
    simp only [checkFrom, Bool.and_eq_true] at h
    exact ih (encloses_cons (checkOp_sound h.1.2 hin hr) hr) h.2

def nonnegOK (nvar : ℕ) (inputs : ℕ → Interval) (rows : List Row) : Bool :=
  !rows.isEmpty && checkFrom nvar inputs [] rows && decide (0 ≤ (getI (boundsFrom [] rows) 0).lo)

noncomputable def eval (xs : ℕ → ℝ) (rows : List Row) : ℝ :=
  (evalFrom xs [] rows).getD 0 0

/-- A complete checked program proves a real inequality on its entire input box. -/
theorem nonneg_sound {nvar : ℕ} {inputs : ℕ → Interval} {rows : List Row} {xs : ℕ → ℝ}
    (h : nonnegOK nvar inputs rows = true) (hin : InDomain inputs xs) : 0 ≤ eval xs rows := by
  simp only [nonnegOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have hb := checkFrom_sound rows hin encloses_nil h.1.2
  have hl : (0 : ℝ) ≤ ((getI (boundsFrom [] rows) 0).lo : ℝ) := by exact_mod_cast h.2
  exact hl.trans (hb 0).1

end D4Bound.CertificateInterval
