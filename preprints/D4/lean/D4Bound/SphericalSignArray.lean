import D4Bound.SphericalSignTree

/-! A nested integer-array implementation of the degree-twelve tensor checks.
The proofs below identify the arithmetic with the existing tensor operations;
successful external computation is never used as an axiom.
-/
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign.Bernstein.ArrayData

abbrev Data := Array (Array (Array ℤ))

def get (a : Data) (i j k : ℕ) : ℤ := (((a[i]?.getD #[])[j]?.getD #[])[k]?).getD 0

def shapeOK (a : Data) : Bool := decide (a.size = 13) &&
  a.all fun row => decide (row.size = 13) && row.all fun line => decide (line.size = 13)
def tensor (a : Data) : Tensor := fun i j k => get a i.val j.val k.val

def sum13 (f : ℕ → ℤ) : ℤ :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12

lemma sum13_eq (f : ℕ → ℤ) : sum13 f = ∑ h : I, f h.val := by
  simp [sum13, Fin.sum_univ_succ]
  <;> ring

def coefficient (right : Bool) (i h : ℕ) : ℤ :=
  if right then
    if i ≤ h then (Nat.choose (12-i) (h-i) : ℤ)*2^i else 0
  else if h ≤ i then (Nat.choose i h : ℤ)*2^(12-i) else 0

inductive Axis where
  | x | y | z
  deriving DecidableEq, Repr

def value (axis : Axis) (right : Bool) (a : Data) (i j k : ℕ) : ℤ :=
  ceil4096 (sum13 fun h => match axis with
    | .x => coefficient right i h * get a h j k
    | .y => coefficient right j h * get a i h k
    | .z => coefficient right k h * get a i j h)

def referenceSplit (axis : Axis) (right : Bool) (p : Tensor) : Tensor :=
  match axis with
  | .x => splitX right p
  | .y => splitY right p
  | .z => splitZ right p

lemma value_eq (axis : Axis) (right : Bool) (a : Data) (i j k : I) :
    value axis right a i.val j.val k.val = referenceSplit axis right (tensor a) i j k := by
  cases axis <;> cases right <;>
    simp only [value, referenceSplit, splitX, splitY, splitZ, swapXY, swapXZ,
      tensor, sum13_eq, coefficient, Bool.false_eq_true, if_false, if_true,
      lcoef, rcoef]

/-- Tabulation preserves the mathematical tensor, but prevents long chains of
unevaluated tensor functions from repeatedly expanding earlier subdivisions. -/
def splitData (axis : Axis) (right : Bool) (a : Data) : Data :=
  Array.ofFn fun i : I => Array.ofFn fun j : I => Array.ofFn fun k : I =>
    value axis right a i.val j.val k.val

lemma tensor_splitData (axis : Axis) (right : Bool) (a : Data) :
    tensor (splitData axis right a) = referenceSplit axis right (tensor a) := by
  funext i j k
  change get (splitData axis right a) i.val j.val k.val = _
  simpa [get, splitData] using value_eq axis right a i j k

def rowCheck (axis : Axis) (right : Bool) (a b : Data) (i : ℕ) : Bool :=
  (List.range 13).all fun j => (List.range 13).all fun k =>
    decide (get b i j k = value axis right a i j k)

def stepCheck (axis : Axis) (right : Bool) (a b : Data) : Bool :=
  (shapeOK a && shapeOK b) &&
    (List.range 13).all (rowCheck axis right a b)

lemma rowCheck_sound (axis : Axis) (right : Bool) (a b : Data) (i : I)
    (h : rowCheck axis right a b i.val = true) (j k : I) :
    tensor b i j k = referenceSplit axis right (tensor a) i j k := by
  simp only [rowCheck, List.all_eq_true] at h
  have he := h j.val (by simpa only [List.mem_range] using j.isLt)
    k.val (by simpa only [List.mem_range] using k.isLt)
  have he' : get b i.val j.val k.val = value axis right a i.val j.val k.val := by
    simpa only [decide_eq_true_eq] using he
  exact he'.trans (value_eq axis right a i j k)

lemma stepCheck_sound (axis : Axis) (right : Bool) (a b : Data)
    (h : stepCheck axis right a b = true) :
    tensor b = referenceSplit axis right (tensor a) := by
  simp only [stepCheck, Bool.and_eq_true, List.all_eq_true] at h
  funext i j k
  exact rowCheck_sound axis right a b i
    (h.2 i.val (by simpa only [List.mem_range] using i.isLt)) j k

def leafCheck (p d : Data) (u v : ℕ) : Bool :=
  (shapeOK p && shapeOK d) &&
    ((decide (0 < v) && (List.range 13).all fun i =>
      (List.range 13).all fun j => (List.range 13).all fun k =>
        decide ((v : ℤ)*get p i j k+(u : ℤ)*get d i j k ≤ 0)) ||
    (List.range 13).all fun i => (List.range 13).all fun j =>
      (List.range 13).all fun k => decide (get d i j k ≤ -1))

lemma leafCheck_sound (p d : Data) (u v : ℕ)
    (h : leafCheck p d u v = true) : OnCube (tensor p) (tensor d) := by
  simp only [leafCheck, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  apply leaf_sound
  simp only [leafOK, Bool.or_eq_true, decide_eq_true_eq]
  rcases h.2 with h | h
  · left
    refine ⟨h.1, ?_⟩
    intro i j k
    exact h.2 i.val (by simpa only [List.mem_range] using i.isLt)
      j.val (by simpa only [List.mem_range] using j.isLt)
      k.val (by simpa only [List.mem_range] using k.isLt)
  · right
    intro i j k
    exact h i.val (by simpa only [List.mem_range] using i.isLt)
      j.val (by simpa only [List.mem_range] using j.isLt)
      k.val (by simpa only [List.mem_range] using k.isLt)

def checkData (p d : Data) : Tree → Bool
  | .leaf u v => leafCheck p d u v
  | .x l r => checkData (splitData .x false p) (splitData .x false d) l &&
      checkData (splitData .x true p) (splitData .x true d) r
  | .y l r => checkData (splitData .y false p) (splitData .y false d) l &&
      checkData (splitData .y true p) (splitData .y true d) r
  | .z l r => checkData (splitData .z false p) (splitData .z false d) l &&
      checkData (splitData .z true p) (splitData .z true d) r

lemma checkData_sound (t : Tree) (p d : Data) (h : checkData p d t = true) :
    OnCube (tensor p) (tensor d) := by
  induction t generalizing p d with
  | leaf u v => exact leafCheck_sound p d u v h
  | x l r ihl ihr =>
    simp only [checkData, Bool.and_eq_true] at h
    apply onCube_splitX
    · simpa only [tensor_splitData, referenceSplit] using ihl _ _ h.1
    · simpa only [tensor_splitData, referenceSplit] using ihr _ _ h.2
  | y l r ihl ihr =>
    simp only [checkData, Bool.and_eq_true] at h
    apply onCube_splitY
    · simpa only [tensor_splitData, referenceSplit] using ihl _ _ h.1
    · simpa only [tensor_splitData, referenceSplit] using ihr _ _ h.2
  | z l r ihl ihr =>
    simp only [checkData, Bool.and_eq_true] at h
    apply onCube_splitZ
    · simpa only [tensor_splitData, referenceSplit] using ihl _ _ h.1
    · simpa only [tensor_splitData, referenceSplit] using ihr _ _ h.2
-- Shape checks fail closed, even when the missing entries would default to zero.
example : stepCheck .x false #[] #[] = false := by decide +kernel
example : leafCheck #[] #[] 0 1 = false := by decide +kernel

end D4Bound.SphericalSign.Bernstein.ArrayData
