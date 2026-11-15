import D4Bound.CyclicNativeArray
import D4Bound.V7CyclicPolynomialBasic

/-!
# Soundness of the native cyclic checker

`checkPoly_sound`: if `checkPoly thr unit w fuel p = true`, every box threshold
`thr B` is below a function `G` on that box, and `G ≥ 0` on the unit cube, then
the sparse polynomial `p` is at most `G` on the whole unit cube.
-/
namespace D4Bound.CyclicNative
open Finset

noncomputable section

/-! ## Boxes -/

def Dy.pt (d : Dy) (u : ℝ) : ℝ := ((d.num : ℝ) + u) / (2:ℝ)^d.lev

lemma Dy.pt_left (d : Dy) (u : ℝ) : d.left.pt u = d.pt (u/2) := by
  simp only [Dy.pt, Dy.left, pow_succ]; push_cast; field_simp; try ring

lemma Dy.pt_right (d : Dy) (u : ℝ) : d.right.pt u = d.pt ((1+u)/2) := by
  simp only [Dy.pt, Dy.right, pow_succ]; push_cast; field_simp; try ring

lemma Dy.pt_mem (d : Dy) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    ((d.lo : ℚ) : ℝ) ≤ d.pt u ∧ d.pt u ≤ ((d.hi : ℚ) : ℝ) := by
  have hp : (0:ℝ) < (2:ℝ)^d.lev := by positivity
  simp only [Dy.pt, Dy.lo, Dy.hi]
  push_cast
  constructor
  · exact div_le_div_of_nonneg_right (by linarith) hp.le
  · exact div_le_div_of_nonneg_right (by linarith) hp.le

lemma rootBox_pt (u : ℝ) : rootBox.a.pt u = u ∧ rootBox.b.pt u = u ∧ rootBox.c.pt u = u := by
  simp [rootBox, Dy.pt]

def Dy.Valid (d : Dy) : Prop := d.num < 2^d.lev
def Box.Valid (B : Box) : Prop := B.a.Valid ∧ B.b.Valid ∧ B.c.Valid

lemma Dy.valid_left {d : Dy} (h : d.Valid) : d.left.Valid := by
  unfold Dy.Valid at *; simp only [Dy.left]; rw [pow_succ]; omega
lemma Dy.valid_right {d : Dy} (h : d.Valid) : d.right.Valid := by
  unfold Dy.Valid at *; simp only [Dy.right]; rw [pow_succ]; omega

lemma rootBox_valid : rootBox.Valid := by
  simp [Box.Valid, Dy.Valid, rootBox]

lemma Dy.pt_unit {d : Dy} (hv : d.Valid) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 ≤ d.pt u ∧ d.pt u ≤ 1 := by
  unfold Dy.pt
  have hp : (0:ℝ) < (2:ℝ)^d.lev := by positivity
  have hn : ((d.num : ℝ) + 1) ≤ (2:ℝ)^d.lev := by
    have : d.num + 1 ≤ 2^d.lev := hv
    exact_mod_cast this
  constructor
  · positivity
  · rw [div_le_one hp]; linarith

lemma Box.valid_split {B : Box} (h : B.Valid) (ax : ℕ) :
    (B.splitAxis ax).1.Valid ∧ (B.splitAxis ax).2.Valid := by
  obtain ⟨ha, hb, hc⟩ := h
  rcases ax with _ | _ | ax
  · exact ⟨⟨Dy.valid_left ha, hb, hc⟩, ⟨Dy.valid_right ha, hb, hc⟩⟩
  · exact ⟨⟨ha, Dy.valid_left hb, hc⟩, ⟨ha, Dy.valid_right hb, hc⟩⟩
  · exact ⟨⟨ha, hb, Dy.valid_left hc⟩, ⟨ha, hb, Dy.valid_right hc⟩⟩

def Cube (x y z : ℝ) : Prop := 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ∧ 0 ≤ z ∧ z ≤ 1

/-- Invariant: the target function on the box is below the scaled Bernstein form. -/
def Inv (f : ℝ → ℝ → ℝ → ℝ) (unit : ℚ) (T : Tens) (B : Box) : Prop :=
  ∀ x y z, Cube x y z → f (B.a.pt x) (B.b.pt y) (B.c.pt z) ≤ (unit : ℝ) * E3 T x y z

lemma leaf_sound {f G : ℝ → ℝ → ℝ → ℝ} {thr : Box → ℚ} {unit : ℚ} (hu : (0:ℝ) ≤ unit)
    {T : Tens} {B : Box} (hinv : Inv f unit T B)
    (hthr : ∀ x y z, Cube x y z → ((thr B : ℚ) : ℝ) ≤ G (B.a.pt x) (B.b.pt y) (B.c.pt z))
    (hG : ∀ x y z, Cube x y z → 0 ≤ G (B.a.pt x) (B.b.pt y) (B.c.pt z))
    (h : (T.top == 0 || decide ((T.top : ℚ) * unit ≤ thr B)) = true) :
    ∀ x y z, Cube x y z → f (B.a.pt x) (B.b.pt y) (B.c.pt z) ≤ G (B.a.pt x) (B.b.pt y) (B.c.pt z) := by
  intro x y z hc
  obtain ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩ := hc
  have h1 := hinv x y z ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩
  have h2 := E3_le_top T hx0 hx1 hy0 hy1 hz0 hz1
  have h3 : (unit : ℝ) * E3 T x y z ≤ (unit : ℝ) * (T.top : ℝ) := mul_le_mul_of_nonneg_left h2 hu
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with h | h
  · rw [h] at h3
    have := hG x y z ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩
    simp at h3
    linarith
  · have h4 : ((T.top : ℚ) * unit : ℚ) ≤ thr B := h
    have h5 : ((T.top : ℝ) * (unit : ℝ)) ≤ ((thr B : ℚ) : ℝ) := by exact_mod_cast h4
    have := hthr x y z ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩
    nlinarith

lemma half_cases {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (0 ≤ 2*x ∧ 2*x ≤ 1 ∧ x = (2*x)/2) ∨ (0 ≤ 2*x-1 ∧ 2*x-1 ≤ 1 ∧ x = (1+(2*x-1))/2) := by
  rcases le_total x (1/2) with h | h
  · left; refine ⟨by linarith, by linarith, by ring⟩
  · right; refine ⟨by linarith, by linarith, by ring⟩

theorem check_sound (thr : Box → ℚ) (unit : ℚ) (w : ℚ × ℚ × ℚ) (hu : (0:ℝ) ≤ unit)
    (f G : ℝ → ℝ → ℝ → ℝ)
    (hthr : ∀ (B : Box), B.Valid → ∀ x y z, Cube x y z →
      ((thr B : ℚ) : ℝ) ≤ G (B.a.pt x) (B.b.pt y) (B.c.pt z))
    (hG : ∀ (B : Box), B.Valid → ∀ x y z, Cube x y z → 0 ≤ G (B.a.pt x) (B.b.pt y) (B.c.pt z)) :
    ∀ fuel T B, B.Valid → check thr unit w fuel T B = true → Inv f unit T B →
      ∀ x y z, Cube x y z → f (B.a.pt x) (B.b.pt y) (B.c.pt z) ≤ G (B.a.pt x) (B.b.pt y) (B.c.pt z) := by
  intro fuel
  induction fuel with
  | zero =>
    intro T B hB h hinv
    exact leaf_sound hu hinv (hthr B hB) (hG B hB) (by simpa [check] using h)
  | succ fuel ih =>
    intro T B hB h hinv
    simp only [check, Bool.or_eq_true] at h
    rcases h with h | h
    · exact leaf_sound hu hinv (hthr B hB) (hG B hB) (by simpa using h)
    simp only [Bool.and_eq_true] at h
    obtain ⟨hl, hr⟩ := h
    set ax := chooseAxis w B
    have hv := Box.valid_split hB ax
    have hax : ax = 0 ∨ ax = 1 ∨ 2 ≤ ax := by omega
    intro x y z hc
    obtain ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩ := hc
    rcases hax with h0 | h0 | h0
    · -- split the first coordinate
      have hL : Inv f unit (splitAxis T ax).1 (B.splitAxis ax).1 := by
        intro x' y' z' hc'
        obtain ⟨a0, a1, b0, b1, c0, c1⟩ := hc'
        have hs := ((E3_splitAxis T ax a0 a1 b0 b1 c0 c1).1 h0).1
        rw [h0] at hs ⊢
        simp only [Box.splitAxis, Dy.pt_left]
        have := hinv (x'/2) y' z' ⟨by linarith, by linarith, b0, b1, c0, c1⟩
        nlinarith
      have hR : Inv f unit (splitAxis T ax).2 (B.splitAxis ax).2 := by
        intro x' y' z' hc'
        obtain ⟨a0, a1, b0, b1, c0, c1⟩ := hc'
        have hs := ((E3_splitAxis T ax a0 a1 b0 b1 c0 c1).1 h0).2
        rw [h0] at hs ⊢
        simp only [Box.splitAxis, Dy.pt_right]
        have := hinv ((1+x')/2) y' z' ⟨by linarith, by linarith, b0, b1, c0, c1⟩
        nlinarith
      rcases half_cases hx0 hx1 with ⟨u0, u1, ue⟩ | ⟨u0, u1, ue⟩
      · have := ih _ _ hv.1 hl hL (2*x) y z ⟨u0, u1, hy0, hy1, hz0, hz1⟩
        rw [h0] at this
        simpa only [Box.splitAxis, Dy.pt_left, ← ue] using this
      · have := ih _ _ hv.2 hr hR (2*x-1) y z ⟨u0, u1, hy0, hy1, hz0, hz1⟩
        rw [h0] at this
        simpa only [Box.splitAxis, Dy.pt_right, ← ue] using this
    · have hL : Inv f unit (splitAxis T ax).1 (B.splitAxis ax).1 := by
        intro x' y' z' hc'
        obtain ⟨a0, a1, b0, b1, c0, c1⟩ := hc'
        have hs := ((E3_splitAxis T ax a0 a1 b0 b1 c0 c1).2.1 h0).1
        rw [h0] at hs ⊢
        simp only [Box.splitAxis, Dy.pt_left]
        have := hinv x' (y'/2) z' ⟨a0, a1, by linarith, by linarith, c0, c1⟩
        nlinarith
      have hR : Inv f unit (splitAxis T ax).2 (B.splitAxis ax).2 := by
        intro x' y' z' hc'
        obtain ⟨a0, a1, b0, b1, c0, c1⟩ := hc'
        have hs := ((E3_splitAxis T ax a0 a1 b0 b1 c0 c1).2.1 h0).2
        rw [h0] at hs ⊢
        simp only [Box.splitAxis, Dy.pt_right]
        have := hinv x' ((1+y')/2) z' ⟨a0, a1, by linarith, by linarith, c0, c1⟩
        nlinarith
      rcases half_cases hy0 hy1 with ⟨u0, u1, ue⟩ | ⟨u0, u1, ue⟩
      · have := ih _ _ hv.1 hl hL x (2*y) z ⟨hx0, hx1, u0, u1, hz0, hz1⟩
        rw [h0] at this
        simpa only [Box.splitAxis, Dy.pt_left, ← ue] using this
      · have := ih _ _ hv.2 hr hR x (2*y-1) z ⟨hx0, hx1, u0, u1, hz0, hz1⟩
        rw [h0] at this
        simpa only [Box.splitAxis, Dy.pt_right, ← ue] using this
    · obtain ⟨m, hm⟩ : ∃ m, ax = m+2 := ⟨ax-2, by omega⟩
      have hL : Inv f unit (splitAxis T ax).1 (B.splitAxis ax).1 := by
        intro x' y' z' hc'
        obtain ⟨a0, a1, b0, b1, c0, c1⟩ := hc'
        have hs := ((E3_splitAxis T ax a0 a1 b0 b1 c0 c1).2.2 h0).1
        rw [hm] at hs ⊢
        simp only [Box.splitAxis, Dy.pt_left]
        have := hinv x' y' (z'/2) ⟨a0, a1, b0, b1, by linarith, by linarith⟩
        nlinarith
      have hR : Inv f unit (splitAxis T ax).2 (B.splitAxis ax).2 := by
        intro x' y' z' hc'
        obtain ⟨a0, a1, b0, b1, c0, c1⟩ := hc'
        have hs := ((E3_splitAxis T ax a0 a1 b0 b1 c0 c1).2.2 h0).2
        rw [hm] at hs ⊢
        simp only [Box.splitAxis, Dy.pt_right]
        have := hinv x' y' ((1+z')/2) ⟨a0, a1, b0, b1, by linarith, by linarith⟩
        nlinarith
      rcases half_cases hz0 hz1 with ⟨u0, u1, ue⟩ | ⟨u0, u1, ue⟩
      · have := ih _ _ hv.1 hl hL x y (2*z) ⟨hx0, hx1, hy0, hy1, u0, u1⟩
        rw [hm] at this
        simpa only [Box.splitAxis, Dy.pt_left, ← ue] using this
      · have := ih _ _ hv.2 hr hR x y (2*z-1) ⟨hx0, hx1, hy0, hy1, u0, u1⟩
        rw [hm] at this
        simpa only [Box.splitAxis, Dy.pt_right, ← ue] using this

/-! ## Initial tensor -/

def pw (k : ℕ) (x : ℝ) : ℝ := x^k
def bp (n k : ℕ) (x : ℝ) : ℝ := x^k*(1-x)^(n-k)

lemma pascal_getD (n : ℕ) : ∀ k, (pascal n).getD k 0 = n.choose k := by
  induction n with
  | zero =>
    intro k
    rcases k with _ | k
    · simp [pascal]
    · simp [pascal]
  | succ n ih =>
    intro k
    by_cases hk : k < n+2
    · simp only [pascal]
      rw [getD_ofFn _ hk]
      rcases k with _ | k
      · simp [ih 0]
      · simp only [Nat.add_sub_cancel, ih k, ih (k+1), Nat.choose_succ_succ', if_neg (Nat.succ_ne_zero k)]
        all_goals ring
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp only [pascal, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
      simp [hk]

lemma binom_eq (n k : ℕ) : binom n k = n.choose k := by
  unfold binom
  split_ifs with h
  · unfold pascalTab
    rw [getD_ofFn _ h]
    exact pascal_getD n k
  · exact pascal_getD n k

lemma foldl_range_sum (F : ℕ → ℤ) (n : ℕ) :
    (List.range n).foldl (fun s l => s + F l) 0 = ∑ l ∈ range n, F l := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, sum_range_succ]; simp

lemma convLast_get (T : Tens) {i j k : ℕ} (hi : i ≤ T.n0) (hj : j ≤ T.n1) (hk : k ≤ T.n2) :
    (convLast T).get i j k = ∑ l ∈ range (k+1), ((T.n2-l).choose (k-l) : ℤ) * T.get i j l := by
  have hlt := idx_lt T hi hj hk
  obtain ⟨hd, hm⟩ := idx_div T (i := i) (j := j) hk
  have hf : i*(T.n1+1)+j < (T.n0+1)*(T.n1+1) := by nlinarith
  show (Array.ofFn _).getD (T.idx i j k) 0 = _
  rw [getD_ofFn _ (by simpa [Tens.idx] using hlt)]
  simp only [hd, hm]
  rw [getD_ofFn _ hf]
  unfold convFiber
  rw [getD_ofFn _ (by omega)]
  simp only
  rw [foldl_range_sum]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ k := by simp at hl; omega
  rw [binom_eq, fiber_getD T (by omega)]

@[simp] lemma convLast_dims (T : Tens) : (convLast T).n0 = T.n0 ∧ (convLast T).n1 = T.n1 ∧
    (convLast T).n2 = T.n2 := by simp [convLast]

lemma S_convLast (T : Tens) (φ0 φ1 : ℕ → ℝ → ℝ) (x y z : ℝ) :
    S (convLast T) φ0 φ1 (bp T.n2) x y z = S T φ0 φ1 pw x y z := by
  unfold S
  simp only [convLast_dims]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have hi' : i ≤ T.n0 := by simp at hi; omega
  have hj' : j ≤ T.n1 := by simp at hj; omega
  have h1 : ∀ k ∈ range (T.n2+1), ((convLast T).get i j k : ℝ) * (φ0 i x * φ1 j y * bp T.n2 k z) =
      (φ0 i x * φ1 j y) * ((∑ l ∈ range (k+1), ((T.n2-l).choose (k-l) : ℝ) * (T.get i j l : ℝ)) *
        (z^k*(1-z)^(T.n2-k))) := by
    intro k hk
    rw [convLast_get T hi' hj' (by simp at hk; omega)]
    push_cast
    unfold bp; ring
  rw [sum_congr rfl h1, ← mul_sum, ← power_to_bernstein, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  unfold pw; ring

lemma S_convAll (T : Tens) (x y z : ℝ) :
    S (convAll T) (bp T.n0) (bp T.n1) (bp T.n2) x y z = S T pw pw pw x y z := by
  unfold convAll
  have e1 := S_convLast T pw pw x y z
  have e2 := S_convLast (rot (convLast T)) pw (bp T.n2) y z x
  have e3 := S_convLast (rot (convLast (rot (convLast T)))) (bp T.n2) (bp T.n0) z x y
  simp only [rot_n0, rot_n1, rot_n2, convLast_dims] at e2 e3
  rw [S_rot, e3, S_rot, e2, S_rot, e1]

lemma S_zero_dims (T : Tens) (hT : ∀ i j k, T.get i j k = 0) (φ0 φ1 φ2 : ℕ → ℝ → ℝ) (x y z : ℝ) :
    S T φ0 φ1 φ2 x y z = 0 := by
  unfold S; simp [hT]

lemma idx_inj (T : Tens) {i j k a b c : ℕ} (hj : j ≤ T.n1) (hk : k ≤ T.n2) (hb : b ≤ T.n1)
    (hc : c ≤ T.n2) (h : T.idx i j k = T.idx a b c) : i = a ∧ j = b ∧ k = c := by
  obtain ⟨d1, m1⟩ := idx_div T (i := i) (j := j) hk
  obtain ⟨d2, m2⟩ := idx_div T (i := a) (j := b) hc
  rw [h] at d1 m1
  have hk' : k = c := by rw [← m1, m2]
  have hf : i*(T.n1+1)+j = a*(T.n1+1)+b := by rw [← d1, d2]
  have e1 : (i*(T.n1+1)+j) % (T.n1+1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have e2 : (a*(T.n1+1)+b) % (T.n1+1) = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have e3 : (i*(T.n1+1)+j) / (T.n1+1) = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; simp
  have e4 : (a*(T.n1+1)+b) / (T.n1+1) = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; simp
  refine ⟨?_, ?_, hk'⟩
  · rw [← e3, hf, e4]
  · rw [← e1, hf, e2]

/-- One accumulation step of `denseOf`. -/
def denseStep (D : ℕ) (T : Tens) (t : (ℕ × ℕ × ℕ) × ℚ) : Tens :=
  ⟨T.n0,T.n1,T.n2, T.data.modify (T.idx t.1.1 t.1.2.1 t.1.2.2) (· + (t.2 * (D : ℚ)).num)⟩

lemma denseStep_get (D : ℕ) (T : Tens) (t : (ℕ × ℕ × ℕ) × ℚ)
    (hsz : T.data.size = (T.n0+1)*(T.n1+1)*(T.n2+1))
    (ht : t.1.1 ≤ T.n0 ∧ t.1.2.1 ≤ T.n1 ∧ t.1.2.2 ≤ T.n2)
    {i j k : ℕ} (hi : i ≤ T.n0) (hj : j ≤ T.n1) (hk : k ≤ T.n2) :
    (denseStep D T t).get i j k = T.get i j k +
      (if (i,j,k) = t.1 then (t.2 * (D : ℚ)).num else 0) := by
  have hlt := idx_lt T hi hj hk
  simp only [denseStep, Tens.get, Tens.idx, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases he : (i,j,k) = t.1
  · rw [if_pos he]
    rw [← he]
    simp only [if_true]
    have : (i*(T.n1+1)+j)*(T.n2+1)+k < T.data.size := by rw [hsz]; simpa [Tens.idx] using hlt
    simp [this]
  · rw [if_neg he, add_zero]
    have hne : ¬ (T.idx t.1.1 t.1.2.1 t.1.2.2 = T.idx i j k) := by
      intro h
      obtain ⟨a, b, c⟩ := idx_inj T ht.2.1 ht.2.2 hj hk h
      exact he (by rw [← a, ← b, ← c])
    simp only [Tens.idx] at hne
    simp [hne]

lemma S_denseStep (D : ℕ) (T : Tens) (t : (ℕ × ℕ × ℕ) × ℚ)
    (hsz : T.data.size = (T.n0+1)*(T.n1+1)*(T.n2+1))
    (ht : t.1.1 ≤ T.n0 ∧ t.1.2.1 ≤ T.n1 ∧ t.1.2.2 ≤ T.n2) (hden : (t.2 * (D : ℚ)).den = 1)
    (x y z : ℝ) :
    S (denseStep D T t) pw pw pw x y z = S T pw pw pw x y z +
      (D : ℝ) * ((t.2 : ℝ) * (x^t.1.1 * y^t.1.2.1 * z^t.1.2.2)) := by
  have hnum : (((t.2 * (D : ℚ)).num : ℤ) : ℝ) = (D : ℝ) * (t.2 : ℝ) := by
    have := Rat.coe_int_num_of_den_eq_one hden
    have h' : ((((t.2 * (D : ℚ)).num : ℚ)) : ℝ) = ((t.2 * (D : ℚ) : ℚ) : ℝ) := by rw [this]
    push_cast at h'
    rw [h']; ring
  unfold S
  simp only [show (denseStep D T t).n0 = T.n0 from rfl, show (denseStep D T t).n1 = T.n1 from rfl,
    show (denseStep D T t).n2 = T.n2 from rfl]
  have h1 : ∀ i ∈ range (T.n0+1), ∀ j ∈ range (T.n1+1), ∀ k ∈ range (T.n2+1),
      ((denseStep D T t).get i j k : ℝ) * (pw i x * pw j y * pw k z) =
      (T.get i j k : ℝ) * (pw i x * pw j y * pw k z) +
      (if (i,j,k) = t.1 then (D : ℝ) * (t.2 : ℝ) * (pw i x * pw j y * pw k z) else 0) := by
    intro i hi j hj k hk
    rw [denseStep_get D T t hsz ht (by simp at hi; omega) (by simp at hj; omega) (by simp at hk; omega)]
    split_ifs <;> push_cast <;> simp [hnum] <;> ring
  rw [show ∑ i ∈ range (T.n0+1), ∑ j ∈ range (T.n1+1), ∑ k ∈ range (T.n2+1),
      ((denseStep D T t).get i j k : ℝ) * (pw i x * pw j y * pw k z) = _ from
    sum_congr rfl fun i hi => sum_congr rfl fun j hj => sum_congr rfl fun k hk => h1 i hi j hj k hk]
  simp only [sum_add_distrib]
  congr 1
  obtain ⟨⟨a, b, c⟩, q⟩ := t
  simp only at ht ⊢
  rw [sum_eq_single a, sum_eq_single b, sum_eq_single c]
  · simp [pw]; ring
  · intro c' _ hc'; simp [hc']
  · intro hc'; simp at hc'; omega
  · intro b' _ hb'; apply sum_eq_zero; intro c' _; simp [hb']
  · intro hb'; simp at hb'; omega
  · intro a' _ ha'; apply sum_eq_zero; intro b' _; apply sum_eq_zero; intro c' _; simp [ha']
  · intro ha'; simp at ha'; omega

lemma denseOf_eq (n0 n1 n2 D : ℕ) (p : List ((ℕ × ℕ × ℕ) × ℚ)) :
    denseOf n0 n1 n2 D p =
      p.foldl (denseStep D) ⟨n0,n1,n2, Array.replicate ((n0+1)*(n1+1)*(n2+1)) 0⟩ := rfl

lemma S_foldl (D : ℕ) (p : List ((ℕ × ℕ × ℕ) × ℚ)) : ∀ (T : Tens),
    T.data.size = (T.n0+1)*(T.n1+1)*(T.n2+1) →
    (∀ t ∈ p, t.1.1 ≤ T.n0 ∧ t.1.2.1 ≤ T.n1 ∧ t.1.2.2 ≤ T.n2) →
    (∀ t ∈ p, (t.2 * (D : ℚ)).den = 1) → ∀ x y z,
    S (p.foldl (denseStep D) T) pw pw pw x y z = S T pw pw pw x y z +
      (D : ℝ) * V7.CyclicPoly.eval p x y z := by
  induction p with
  | nil => intro T _ _ _ x y z; simp [V7.CyclicPoly.eval]
  | cons t p ih =>
    intro T hsz hdeg hden x y z
    simp only [List.foldl_cons]
    have hsz' : (denseStep D T t).data.size =
        ((denseStep D T t).n0+1)*((denseStep D T t).n1+1)*((denseStep D T t).n2+1) := by
      simp [denseStep, hsz]
    rw [ih (denseStep D T t) hsz' (fun t' ht' => hdeg t' (List.mem_cons_of_mem _ ht'))
      (fun t' ht' => hden t' (List.mem_cons_of_mem _ ht')),
      S_denseStep D T t hsz (hdeg t List.mem_cons_self) (hden t List.mem_cons_self)]
    simp only [V7.CyclicPoly.eval_cons, V7.CyclicPoly.termEval, V7.CyclicPoly.monomial]
    ring

lemma rceil_ge (q : ℚ) : (q : ℝ) ≤ (rceil q : ℝ) := by
  have hd : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have h1 : ((-q.num) / (q.den : ℤ)) * (q.den : ℤ) ≤ -q.num := Int.ediv_mul_le _ (ne_of_gt hd)
  have h2 : q.num ≤ (rceil q) * q.den := by unfold rceil; linarith
  have h3 : (q.num : ℝ) ≤ (rceil q : ℝ) * (q.den : ℝ) := by exact_mod_cast h2
  have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  rw [hq, div_le_iff₀ (by exact_mod_cast q.den_pos)]
  exact h3

@[simp] lemma scaleUp_dims (T : Tens) (D : ℕ) (u : ℚ) : (scaleUp T D u).n0 = T.n0 ∧
    (scaleUp T D u).n1 = T.n1 ∧ (scaleUp T D u).n2 = T.n2 := by simp [scaleUp]

lemma scaleUp_get (T : Tens) (D : ℕ) (u : ℚ) {i j k : ℕ} (hi : i ≤ T.n0) (hj : j ≤ T.n1)
    (hk : k ≤ T.n2) : (scaleUp T D u).get i j k =
      rceil ((T.get i j k : ℚ) / ((D * binom T.n0 i * binom T.n1 j * binom T.n2 k : ℕ) * u)) := by
  have hlt := idx_lt T hi hj hk
  obtain ⟨hd, hm⟩ := idx_div T (i := i) (j := j) hk
  have e1 : (i*(T.n1+1)+j) % (T.n1+1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have e2 : (i*(T.n1+1)+j) / (T.n1+1) = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; simp
  show (Array.ofFn _).getD (T.idx i j k) 0 = _
  rw [getD_ofFn _ (by simpa [Tens.idx] using hlt)]
  simp only [hd, hm, e1, e2]

lemma initial_inv (p : List ((ℕ × ℕ × ℕ) × ℚ)) (unit : ℚ) (hu : 0 < unit)
    (hdeg : degreesOK (degrees p).1 (degrees p).2.1 (degrees p).2.2 p = true)
    (hint : intOK (commonDen p) p = true) :
    Inv (fun x y z => V7.CyclicPoly.eval p x y z) unit (initial p unit) rootBox := by
  intro x y z hc
  obtain ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩ := hc
  dsimp only
  rw [(rootBox_pt x).1, (rootBox_pt y).2.1, (rootBox_pt z).2.2]
  set d := degrees p
  set D := commonDen p
  set A := denseOf d.1 d.2.1 d.2.2 D p
  have hD : (0 : ℝ) < D := by
    have : 0 < D := by
      simp only [D, commonDen]
      have key : ∀ (l : List ((ℕ × ℕ × ℕ) × ℚ)) (a : ℕ), 0 < a → 0 < l.foldl (fun d t => Nat.lcm d t.2.den) a := by
        intro l
        induction l with
        | nil => intro a ha; simpa using ha
        | cons t l ih => intro a ha; exact ih _ (Nat.lcm_pos ha t.2.den_pos)
      exact key p 1 (by norm_num)
    exact_mod_cast this
  have hdeg' : ∀ t ∈ p, t.1.1 ≤ d.1 ∧ t.1.2.1 ≤ d.2.1 ∧ t.1.2.2 ≤ d.2.2 := by
    intro t ht
    have := List.all_eq_true.mp hdeg t ht
    simpa using this
  have hden : ∀ t ∈ p, (t.2 * (D : ℚ)).den = 1 := by
    intro t ht
    have := List.all_eq_true.mp hint t ht
    simpa using this
  have hA := S_foldl D p ⟨d.1, d.2.1, d.2.2, Array.replicate ((d.1+1)*(d.2.1+1)*(d.2.2+1)) 0⟩
    (by simp) hdeg' hden x y z
  rw [S_zero_dims ⟨d.1, d.2.1, d.2.2, Array.replicate ((d.1+1)*(d.2.1+1)*(d.2.2+1)) 0⟩
    (by intro i j k; simp only [Tens.get, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
        split_ifs <;> rfl), zero_add, ← denseOf_eq] at hA
  have hC := S_convAll A x y z
  rw [hA] at hC
  -- compare with the rounded tensor
  have hmain : V7.CyclicPoly.eval p x y z =
      S (convAll A) (bp A.n0) (bp A.n1) (bp A.n2) x y z / D := by
    rw [hC]; field_simp
  rw [hmain]
  unfold initial
  simp only []
  unfold E3 S
  simp only [scaleUp_dims]
  have hdims : (convAll A).n0 = A.n0 ∧ (convAll A).n1 = A.n1 ∧ (convAll A).n2 = A.n2 := by
    simp [convAll]
  rw [div_eq_mul_inv, sum_mul, mul_sum]
  rw [hdims.1, hdims.2.1, hdims.2.2]
  refine sum_le_sum fun i hi => ?_
  rw [sum_mul, mul_sum]
  refine sum_le_sum fun j hj => ?_
  rw [sum_mul, mul_sum]
  refine sum_le_sum fun k hk => ?_
  have hi' : i ≤ A.n0 := by simp at hi; omega
  have hj' : j ≤ A.n1 := by simp at hj; omega
  have hk' : k ≤ A.n2 := by simp at hk; omega
  rw [scaleUp_get _ D unit (by rw [hdims.1]; exact hi') (by rw [hdims.2.1]; exact hj')
    (by rw [hdims.2.2]; exact hk'), hdims.1, hdims.2.1, hdims.2.2]
  simp only [binom_eq]
  set c := (convAll A).get i j k
  have hb0 : (0:ℝ) < (A.n0.choose i : ℝ) := by exact_mod_cast Nat.choose_pos hi'
  have hb1 : (0:ℝ) < (A.n1.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj'
  have hb2 : (0:ℝ) < (A.n2.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk'
  have hur : (0:ℝ) < (unit : ℝ) := by exact_mod_cast hu
  set q : ℚ := (c : ℚ) / ((D * A.n0.choose i * A.n1.choose j * A.n2.choose k : ℕ) * unit) with hqdef
  have hr := rceil_ge q
  have hqc : (q : ℝ) = (c : ℝ) / ((D:ℝ) * (A.n0.choose i : ℝ) * (A.n1.choose j : ℝ) *
      (A.n2.choose k : ℝ) * (unit : ℝ)) := by rw [hqdef]; push_cast; ring
  rw [hqc] at hr
  have hx := B_nonneg A.n0 i hx0 hx1
  have hy := B_nonneg A.n1 j hy0 hy1
  have hz := B_nonneg A.n2 k hz0 hz1
  have hprod : 0 ≤ B A.n0 i x * B A.n1 j y * B A.n2 k z := by positivity
  have hq : (c : ℝ) / (D * A.n0.choose i * A.n1.choose j * A.n2.choose k * unit) * unit *
      (B A.n0 i x * B A.n1 j y * B A.n2 k z) =
      (c : ℝ) * (bp A.n0 i x * bp A.n1 j y * bp A.n2 k z) * (D:ℝ)⁻¹ := by
    unfold B bp; field_simp
  calc (c : ℝ) * (bp A.n0 i x * bp A.n1 j y * bp A.n2 k z) * (D:ℝ)⁻¹
      = (c : ℝ) / (D * A.n0.choose i * A.n1.choose j * A.n2.choose k * unit) * unit *
          (B A.n0 i x * B A.n1 j y * B A.n2 k z) := hq.symm
    _ ≤ (unit : ℝ) * ((rceil q : ℝ) * (B A.n0 i x * B A.n1 j y * B A.n2 k z)) := by
        rw [show (unit : ℝ) * ((rceil q : ℝ) * (B A.n0 i x * B A.n1 j y * B A.n2 k z)) =
          (rceil q : ℝ) * unit * (B A.n0 i x * B A.n1 j y * B A.n2 k z) by ring]
        apply mul_le_mul_of_nonneg_right _ hprod
        apply mul_le_mul_of_nonneg_right _ hur.le
        exact hr

theorem checkPoly_sound (thr : Box → ℚ) (unit : ℚ) (w : ℚ × ℚ × ℚ) (fuel : ℕ)
    (p : List ((ℕ × ℕ × ℕ) × ℚ)) (G : ℝ → ℝ → ℝ → ℝ)
    (h : checkPoly thr unit w fuel p = true)
    (hthr : ∀ (B : Box), B.Valid → ∀ x y z, Cube x y z →
      ((thr B : ℚ) : ℝ) ≤ G (B.a.pt x) (B.b.pt y) (B.c.pt z))
    (hG : ∀ x y z, Cube x y z → 0 ≤ G x y z) :
    ∀ x y z, Cube x y z → V7.CyclicPoly.eval p x y z ≤ G x y z := by
  simp only [checkPoly, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hdeg, hint⟩, hu⟩, hc⟩ := h
  have hG' : ∀ (B : Box), B.Valid → ∀ x y z, Cube x y z → 0 ≤ G (B.a.pt x) (B.b.pt y) (B.c.pt z) := by
    intro B hB x y z hc
    obtain ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩ := hc
    obtain ⟨ha, hb, hcc⟩ := hB
    exact hG _ _ _ ⟨(Dy.pt_unit ha hx0 hx1).1, (Dy.pt_unit ha hx0 hx1).2, (Dy.pt_unit hb hy0 hy1).1,
      (Dy.pt_unit hb hy0 hy1).2, (Dy.pt_unit hcc hz0 hz1).1, (Dy.pt_unit hcc hz0 hz1).2⟩
  intro x y z hcube
  have := check_sound thr unit w (by exact_mod_cast hu.le) (fun x y z => V7.CyclicPoly.eval p x y z) G
    hthr hG' fuel _ rootBox rootBox_valid hc (initial_inv p unit hu hdeg hint) x y z hcube
  simpa only [(rootBox_pt x).1, (rootBox_pt y).2.1, (rootBox_pt z).2.2] using this

end
end D4Bound.CyclicNative

#print axioms D4Bound.CyclicNative.checkPoly_sound
