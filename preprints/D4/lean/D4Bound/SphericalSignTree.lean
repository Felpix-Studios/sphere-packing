import D4Bound.SphericalSignTensor
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign.Bernstein

def OnCube (p d : Tensor) : Prop := ∀ x y z : ℝ,
  0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ z → z ≤ 1 → Good p d x y z

lemma Good.of_bounds {P D P' D' : ℝ} (hp : P ≤ P') (hd : D ≤ D')
    (h : D'<0 ∨ P'≤0) : D<0 ∨ P≤0 := h.elim (fun hh => Or.inl (lt_of_le_of_lt hd hh)) (fun hh => Or.inr (hp.trans hh))

lemma onCube_splitX (p d : Tensor)
    (hl : OnCube (splitX false p) (splitX false d))
    (hr : OnCube (splitX true p) (splitX true d)) : OnCube p d := by
  intro x y z hx hx1 hy hy1 hz hz1
  by_cases hm : x ≤ 1/2
  · have hw0 : 0 ≤ 2*x := by linarith
    have hw1 : 2*x ≤ 1 := by linarith
    have hP := ev_splitX false p hw0 hw1 hy hy1 hz hz1
    have hD := ev_splitX false d hw0 hw1 hy hy1 hz hz1
    have hg := hl (2*x) y z hw0 hw1 hy hy1 hz hz1
    have he : (2*x)/2=x := by ring
    simpa only [Bool.false_eq_true,if_false,he,Good] using Good.of_bounds hP hD hg
  · have hw0 : 0 ≤ 2*x-1 := by linarith
    have hw1 : 2*x-1 ≤ 1 := by linarith
    have hP := ev_splitX true p hw0 hw1 hy hy1 hz hz1
    have hD := ev_splitX true d hw0 hw1 hy hy1 hz hz1
    have hg := hr (2*x-1) y z hw0 hw1 hy hy1 hz hz1
    have he : (2*x-1+1)/2=x := by ring
    simpa only [if_true,he,Good] using Good.of_bounds hP hD hg

lemma onCube_swapXY (p d : Tensor) : OnCube (swapXY p) (swapXY d) ↔ OnCube p d := by
  constructor <;> intro h x y z hx hx1 hy hy1 hz hz1
  · simpa only [Good,ev_swapXY] using h y x z hy hy1 hx hx1 hz hz1
  · simpa only [Good,ev_swapXY] using h y x z hy hy1 hx hx1 hz hz1

lemma onCube_swapXZ (p d : Tensor) : OnCube (swapXZ p) (swapXZ d) ↔ OnCube p d := by
  constructor <;> intro h x y z hx hx1 hy hy1 hz hz1
  · simpa only [Good,ev_swapXZ] using h z y x hz hz1 hy hy1 hx hx1
  · simpa only [Good,ev_swapXZ] using h z y x hz hz1 hy hy1 hx hx1

lemma onCube_splitY (p d : Tensor)
    (hl : OnCube (splitY false p) (splitY false d))
    (hr : OnCube (splitY true p) (splitY true d)) : OnCube p d := by
  apply (onCube_swapXY p d).mp
  apply onCube_splitX
  · exact (onCube_swapXY _ _).mp hl
  · exact (onCube_swapXY _ _).mp hr

lemma onCube_splitZ (p d : Tensor)
    (hl : OnCube (splitZ false p) (splitZ false d))
    (hr : OnCube (splitZ true p) (splitZ true d)) : OnCube p d := by
  apply (onCube_swapXZ p d).mp
  apply onCube_splitX
  · exact (onCube_swapXZ _ _).mp hl
  · exact (onCube_swapXZ _ _).mp hr

inductive Tree where
  | leaf (u v : ℕ)
  | x (left right : Tree)
  | y (left right : Tree)
  | z (left right : Tree)
  deriving Repr

def leafOK (p d : Tensor) (u v : ℕ) : Bool :=
  decide (0<v ∧ ∀ i j k, combine v u p d i j k ≤ 0) || decide (∀ i j k, d i j k ≤ -1)

def check (p d : Tensor) : Tree → Bool
  | .leaf u v => leafOK p d u v
  | .x l r => check (splitX false p) (splitX false d) l && check (splitX true p) (splitX true d) r
  | .y l r => check (splitY false p) (splitY false d) l && check (splitY true p) (splitY true d) r
  | .z l r => check (splitZ false p) (splitZ false d) l && check (splitZ true p) (splitZ true d) r

lemma leaf_sound {p d : Tensor} {u v : ℕ} (h : leafOK p d u v = true) : OnCube p d := by
  intro x y z hx hx1 hy hy1 hz hz1
  simp only [leafOK,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with h | h
  · exact multiplier_sound p d v u h.1 h.2 hx hx1 hy hy1 hz hz1
  · exact excluded_sound p d h hx hx1 hy hy1 hz hz1

lemma check_sound (t : Tree) (p d : Tensor) (h : check p d t = true) : OnCube p d := by
  induction t generalizing p d with
  | leaf u v => exact leaf_sound h
  | x l r ihl ihr =>
    simp only [check,Bool.and_eq_true] at h
    exact onCube_splitX p d (ihl _ _ h.1) (ihr _ _ h.2)
  | y l r ihl ihr =>
    simp only [check,Bool.and_eq_true] at h
    exact onCube_splitY p d (ihl _ _ h.1) (ihr _ _ h.2)
  | z l r ihl ihr =>
    simp only [check,Bool.and_eq_true] at h
    exact onCube_splitZ p d (ihl _ _ h.1) (ihr _ _ h.2)

#print axioms check_sound
end D4Bound.SphericalSign.Bernstein
