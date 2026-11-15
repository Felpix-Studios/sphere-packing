import D4Bound.CyclicNativeCore
import D4Bound.CyclicNativeBernstein

/-!
# Soundness of the array operations of the native cyclic checker

Each executable array function of `CyclicNativeCore` is related to the exact
real Bernstein identities of `CyclicNativeBernstein`.
-/
namespace D4Bound.CyclicNative
open Finset

lemma getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) {i : ℕ} (h : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getElem?_ofFn, h]

lemma cavg_ge (a b : ℤ) : a + b ≤ 2 * cavg a b := by
  unfold cavg; omega

lemma cavg_ge_real (a b : ℤ) : ((a : ℝ) + b)/2 ≤ (cavg a b : ℝ) := by
  have h := cavg_ge a b
  have h' : ((a + b : ℤ) : ℝ) ≤ ((2 * cavg a b : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- Integer ceil-rounded de Casteljau triangle. -/
def tri (g : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, i => g i
  | l+1, i => cavg (tri g l i) (tri g l (i+1))

lemma triR_le_tri (g : ℕ → ℤ) (l : ℕ) : ∀ i, triR (fun m => (g m : ℝ)) l i ≤ (tri g l i : ℝ) := by
  induction l with
  | zero => intro i; simp [triR, tri]
  | succ l ih =>
    intro i
    simp only [triR, tri]
    have := cavg_ge_real (tri g l i) (tri g l (i+1))
    linarith [ih i, ih (i+1)]

lemma triStep_size (row : Array ℤ) : (triStep row).size = row.size - 1 := by
  simp [triStep]

lemma triStep_getD (row : Array ℤ) {m : ℕ} (h : m+1 < row.size) :
    (triStep row).getD m 0 = cavg (row.getD m 0) (row.getD (m+1) 0) := by
  unfold triStep
  rw [getD_ofFn _ (by omega)]

lemma triLoop_spec (n : ℕ) (g : ℕ → ℤ) : ∀ k l (row L R : Array ℤ), l + k = n →
    row.size = n + 1 - l → (∀ m < row.size, row.getD m 0 = tri g l m) →
    (triLoop k row L R).1.size = L.size + k + 1 ∧
    (triLoop k row L R).2.size = R.size + k + 1 ∧
    (∀ a ≤ k, (triLoop k row L R).1[L.size + a]? = some (tri g (l+a) 0)) ∧
    (∀ a ≤ k, (triLoop k row L R).2[R.size + a]? = some (tri g (l+a) (n-l-a))) := by
  intro k
  induction k with
  | zero =>
    intro l row L R hlk hs hrow
    have h0 : row.getD 0 0 = tri g l 0 := hrow 0 (by omega)
    have h1 : row.getD (row.size-1) 0 = tri g l (n-l) := by
      rw [hrow _ (by omega)]; congr 1; omega
    refine ⟨by simp [triLoop], by simp [triLoop], ?_, ?_⟩
    · intro a ha
      have : a = 0 := by omega
      subst this
      simp [triLoop, Array.getElem?_push, h0]
    · intro a ha
      have : a = 0 := by omega
      subst this
      simp [triLoop, Array.getElem?_push, h1]
  | succ k ih =>
    intro l row L R hlk hs hrow
    have h0 : row.getD 0 0 = tri g l 0 := hrow 0 (by omega)
    have h1 : row.getD (row.size-1) 0 = tri g l (n-l) := by
      rw [hrow _ (by omega)]; congr 1; omega
    have hs' : (triStep row).size = n + 1 - (l+1) := by rw [triStep_size]; omega
    have hrow' : ∀ m < (triStep row).size, (triStep row).getD m 0 = tri g (l+1) m := by
      intro m hm
      rw [triStep_size] at hm
      rw [triStep_getD row (by omega), hrow m (by omega), hrow (m+1) (by omega)]
      rfl
    obtain ⟨e1, e2, e3, e4⟩ := ih (l+1) (triStep row) (L.push (row.getD 0 0))
      (R.push (row.getD (row.size-1) 0)) (by omega) hs' hrow'
    simp only [Array.size_push] at e1 e2 e3 e4
    refine ⟨by simp only [triLoop]; rw [e1]; omega, by simp only [triLoop]; rw [e2]; omega, ?_, ?_⟩
    · intro a ha
      simp only [triLoop]
      rcases Nat.eq_zero_or_eq_succ_pred a with h | h
      · subst h
        have hlt : L.size + 0 < (L.push (row.getD 0 0)).size + k + 1 := by simp; omega
        -- the first new entry is preserved by later pushes
        have keep : ∀ (k' : ℕ) (l' : ℕ) (row' L' R' : Array ℤ) (b : ℕ), b < L'.size →
            (triLoop k' row' L' R').1[b]? = L'[b]? := by
          intro k'
          induction k' with
          | zero => intro l' row' L' R' b hb; simp [triLoop, Array.getElem?_push, show b ≠ L'.size by omega]
          | succ k' ihk =>
            intro l' row' L' R' b hb
            simp only [triLoop]
            rw [ihk l' _ _ _ b (by simp; omega)]
            simp [Array.getElem?_push, show b ≠ L'.size by omega]
        rw [keep k (l+1) _ _ _ (L.size+0) (by simp)]
        simp [Array.getElem?_push, h0]
      · have := e3 (a-1) (by omega)
        rw [show L.size + a = L.size + 1 + (a-1) by omega, this]
        congr 2; omega
    · intro a ha
      simp only [triLoop]
      rcases Nat.eq_zero_or_eq_succ_pred a with h | h
      · subst h
        have keep : ∀ (k' : ℕ) (row' L' R' : Array ℤ) (b : ℕ), b < R'.size →
            (triLoop k' row' L' R').2[b]? = R'[b]? := by
          intro k'
          induction k' with
          | zero => intro row' L' R' b hb; simp [triLoop, Array.getElem?_push, show b ≠ R'.size by omega]
          | succ k' ihk =>
            intro row' L' R' b hb
            simp only [triLoop]
            rw [ihk _ _ _ b (by simp; omega)]
            simp [Array.getElem?_push, show b ≠ R'.size by omega]
        rw [keep k _ _ _ (R.size+0) (by simp)]
        simp [Array.getElem?_push, h1]
      · have := e4 (a-1) (by omega)
        rw [show R.size + a = R.size + 1 + (a-1) by omega, this]
        congr 2 <;> omega

lemma splitFiber_spec (n : ℕ) (g : Array ℤ) (hg : g.size = n+1) :
    (∀ i ≤ n, (splitFiber n g).1.getD i 0 = tri (fun m => g.getD m 0) i 0) ∧
    (∀ i ≤ n, (splitFiber n g).2.getD i 0 = tri (fun m => g.getD m 0) (n-i) i) := by
  obtain ⟨e1, e2, e3, e4⟩ := triLoop_spec n (fun m => g.getD m 0) n 0 g #[] #[] (by omega)
    (by omega) (fun m _ => rfl)
  simp only [Array.size_empty, zero_add] at e1 e2 e3 e4
  constructor
  · intro i hi
    simp only [splitFiber, Array.getD_eq_getD_getElem?, e3 i hi, Option.getD_some]
  · intro i hi
    have hsz : (triLoop n g #[] #[]).2.size = n+1 := e2
    have h4 := e4 (n-i) (by omega)
    have hrev : (triLoop n g #[] #[]).2.reverse[i]? = (triLoop n g #[] #[]).2[n-i]? :=
      Array.getElem?_reverse' (by omega)
    rw [show n - 0 - (n-i) = i by omega] at h4
    simp only [splitFiber, Array.getD_eq_getD_getElem?, hrev, h4, Option.getD_some]

/-! ## Tensors -/

noncomputable section

/-- Trilinear form with arbitrary basis functions on each axis. -/
def S (T : Tens) (φ0 φ1 φ2 : ℕ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  ∑ i ∈ range (T.n0+1), ∑ j ∈ range (T.n1+1), ∑ k ∈ range (T.n2+1),
    (T.get i j k : ℝ) * (φ0 i x * φ1 j y * φ2 k z)

/-- Bernstein form of a tensor. -/
def E3 (T : Tens) (x y z : ℝ) : ℝ := S T (B T.n0) (B T.n1) (B T.n2) x y z

lemma S_congr {T T' : Tens} (h0 : T.n0 = T'.n0) (h1 : T.n1 = T'.n1) (h2 : T.n2 = T'.n2)
    (hg : ∀ i ≤ T.n0, ∀ j ≤ T.n1, ∀ k ≤ T.n2, T.get i j k = T'.get i j k)
    (φ0 φ1 φ2 : ℕ → ℝ → ℝ) (x y z : ℝ) : S T φ0 φ1 φ2 x y z = S T' φ0 φ1 φ2 x y z := by
  unfold S
  rw [← h0, ← h1, ← h2]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => sum_congr rfl fun k hk => ?_
  rw [hg i (by simp at hi; omega) j (by simp at hj; omega) k (by simp at hk; omega)]

lemma S_mono {T T' : Tens} (h0 : T.n0 = T'.n0) (h1 : T.n1 = T'.n1) (h2 : T.n2 = T'.n2)
    (hg : ∀ i ≤ T.n0, ∀ j ≤ T.n1, ∀ k ≤ T.n2, T.get i j k ≤ T'.get i j k)
    {φ0 φ1 φ2 : ℕ → ℝ → ℝ} {x y z : ℝ}
    (hφ : ∀ i j k, 0 ≤ φ0 i x * φ1 j y * φ2 k z) : S T φ0 φ1 φ2 x y z ≤ S T' φ0 φ1 φ2 x y z := by
  unfold S
  rw [← h0, ← h1, ← h2]
  refine sum_le_sum fun i hi => sum_le_sum fun j hj => sum_le_sum fun k hk => ?_
  have := hg i (by simp at hi; omega) j (by simp at hj; omega) k (by simp at hk; omega)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (hφ i j k)

lemma idx_lt (T : Tens) {i j k : ℕ} (hi : i ≤ T.n0) (hj : j ≤ T.n1) (hk : k ≤ T.n2) :
    T.idx i j k < (T.n0+1)*(T.n1+1)*(T.n2+1) := by
  unfold Tens.idx
  have h1 : i*(T.n1+1)+j < (T.n0+1)*(T.n1+1) := by nlinarith
  nlinarith

lemma idx_div (T : Tens) {i j k : ℕ} (hk : k ≤ T.n2) :
    T.idx i j k / (T.n2+1) = i*(T.n1+1)+j ∧ T.idx i j k % (T.n2+1) = k := by
  unfold Tens.idx
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; simp
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

lemma fiber_getD (T : Tens) {i j m : ℕ} (hm : m ≤ T.n2) :
    (T.fiber (i*(T.n1+1)+j)).getD m 0 = T.get i j m := by
  unfold Tens.fiber Tens.get Tens.idx
  rw [getD_ofFn _ (by omega)]

lemma fiber_size (T : Tens) (f : ℕ) : (T.fiber f).size = T.n2+1 := by
  simp [Tens.fiber]

/-- Entries of both halves of a last-axis split. -/
lemma splitLast_get (T : Tens) {i j k : ℕ} (hi : i ≤ T.n0) (hj : j ≤ T.n1) (hk : k ≤ T.n2) :
    (splitLast T).1.get i j k = tri (fun m => T.get i j m) k 0 ∧
    (splitLast T).2.get i j k = tri (fun m => T.get i j m) (T.n2-k) k := by
  have hlt := idx_lt T hi hj hk
  obtain ⟨hd, hm⟩ := idx_div T (i := i) (j := j) hk
  have hf : i*(T.n1+1)+j < (T.n0+1)*(T.n1+1) := by nlinarith
  have hfib : (fun m => (T.fiber (i*(T.n1+1)+j)).getD m 0) = fun m =>
      (T.fiber (i*(T.n1+1)+j)).getD m 0 := rfl
  obtain ⟨sl, sr⟩ := splitFiber_spec T.n2 (T.fiber (i*(T.n1+1)+j)) (fiber_size T _)
  have htri : ∀ l c, c + l ≤ T.n2 → tri (fun m => (T.fiber (i*(T.n1+1)+j)).getD m 0) l c =
      tri (fun m => T.get i j m) l c := by
    intro l
    induction l with
    | zero => intro c hc; simp only [tri]; exact fiber_getD T (by omega)
    | succ l ih => intro c hc; simp only [tri]; rw [ih c (by omega), ih (c+1) (by omega)]
  constructor
  · show (Array.ofFn _).getD (T.idx i j k) 0 = _
    rw [getD_ofFn _ (by simpa [Tens.idx] using hlt)]
    simp only [hd, hm]
    rw [getD_ofFn _ hf, sl k hk, htri k 0 (by omega)]
  · show (Array.ofFn _).getD (T.idx i j k) 0 = _
    rw [getD_ofFn _ (by simpa [Tens.idx] using hlt)]
    simp only [hd, hm]
    rw [getD_ofFn _ hf, sr k hk, htri _ k (by omega)]

lemma e1_get (T : Tens) (i j : ℕ) (z : ℝ) :
    ∑ k ∈ range (T.n2+1), (T.get i j k : ℝ) * B T.n2 k z = e1 T.n2 (fun k => (T.get i j k : ℝ)) z := rfl

lemma E3_eq_e1 (T : Tens) (x y z : ℝ) : E3 T x y z = ∑ i ∈ range (T.n0+1), ∑ j ∈ range (T.n1+1),
    B T.n0 i x * B T.n1 j y * e1 T.n2 (fun k => (T.get i j k : ℝ)) z := by
  unfold E3 S e1
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  ring

lemma E3_splitLast_left (T : Tens) {x y z : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    E3 T x y (z/2) ≤ E3 (splitLast T).1 x y z := by
  rw [E3_eq_e1, E3_eq_e1]
  simp only [splitLast]
  refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
  have hi' : i ≤ T.n0 := by simp at hi; omega
  have hj' : j ≤ T.n1 := by simp at hj; omega
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (B_nonneg _ _ hx0 hx1) (B_nonneg _ _ hy0 hy1))
  rw [e1_left]
  apply e1_mono _ _ hz0 hz1
  intro k hk
  have := (splitLast_get T hi' hj' hk).1
  simp only [splitLast] at this
  rw [this]
  exact triR_le_tri _ k 0

lemma E3_splitLast_right (T : Tens) {x y z : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    E3 T x y ((1+z)/2) ≤ E3 (splitLast T).2 x y z := by
  rw [E3_eq_e1, E3_eq_e1]
  simp only [splitLast]
  refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
  have hi' : i ≤ T.n0 := by simp at hi; omega
  have hj' : j ≤ T.n1 := by simp at hj; omega
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (B_nonneg _ _ hx0 hx1) (B_nonneg _ _ hy0 hy1))
  rw [e1_right]
  apply e1_mono _ _ hz0 hz1
  intro k hk
  have := (splitLast_get T hi' hj' hk).2
  simp only [splitLast] at this
  rw [this]
  exact triR_le_tri _ _ k

lemma rot_get (T : Tens) {a b c : ℕ} (ha : a ≤ T.n1) (hb : b ≤ T.n2) (hc : c ≤ T.n0) :
    (rot T).get a b c = T.get c a b := by
  have hlt := idx_lt (rot T) (i := a) (j := b) (k := c) ha hb hc
  simp only [rot, Tens.get, Tens.idx] at hlt ⊢
  rw [getD_ofFn _ (by simpa using hlt)]
  have e1 : ((a*(T.n2+1)+b)*(T.n0+1)+c) % (T.n0+1) = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have e2 : ((a*(T.n2+1)+b)*(T.n0+1)+c) / (T.n0+1) = a*(T.n2+1)+b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; simp
  have e3 : (a*(T.n2+1)+b) / (T.n2+1) = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; simp
  have e4 : (a*(T.n2+1)+b) % (T.n2+1) = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  simp only [e1, e2, e3, e4]

@[simp] lemma rot_n0 (T : Tens) : (rot T).n0 = T.n1 := rfl
@[simp] lemma rot_n1 (T : Tens) : (rot T).n1 = T.n2 := rfl
@[simp] lemma rot_n2 (T : Tens) : (rot T).n2 = T.n0 := rfl

lemma S_rot (T : Tens) (φ0 φ1 φ2 : ℕ → ℝ → ℝ) (x y z : ℝ) :
    S (rot T) φ1 φ2 φ0 x y z = S T φ0 φ1 φ2 z x y := by
  unfold S
  simp only [rot_n0, rot_n1, rot_n2]
  have h : ∀ a ∈ range (T.n1+1), ∀ b ∈ range (T.n2+1), ∀ c ∈ range (T.n0+1),
      ((rot T).get a b c : ℝ) * (φ1 a x * φ2 b y * φ0 c z) =
      (T.get c a b : ℝ) * (φ0 c z * φ1 a x * φ2 b y) := by
    intro a ha b hb c hc
    rw [rot_get T (by simp at ha; omega) (by simp at hb; omega) (by simp at hc; omega)]
    ring
  rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => sum_congr rfl fun c hc => h a ha b hb c hc]
  rw [sum_congr rfl (fun a _ => sum_comm), sum_comm]

lemma E3_rot (T : Tens) (x y z : ℝ) : E3 (rot T) x y z = E3 T z x y := by
  unfold E3
  simp only [rot_n0, rot_n1, rot_n2]
  exact S_rot T _ _ _ x y z

@[simp] lemma splitLast_dims (T : Tens) : (splitLast T).1.n0 = T.n0 ∧ (splitLast T).1.n1 = T.n1 ∧
    (splitLast T).1.n2 = T.n2 ∧ (splitLast T).2.n0 = T.n0 ∧ (splitLast T).2.n1 = T.n1 ∧
    (splitLast T).2.n2 = T.n2 := by simp [splitLast]

/-- The three split directions. Points are in tensor order. -/
lemma E3_splitAxis (T : Tens) (ax : ℕ) {x y z : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (ax = 0 → E3 T (x/2) y z ≤ E3 (splitAxis T ax).1 x y z ∧
      E3 T ((1+x)/2) y z ≤ E3 (splitAxis T ax).2 x y z) ∧
    (ax = 1 → E3 T x (y/2) z ≤ E3 (splitAxis T ax).1 x y z ∧
      E3 T x ((1+y)/2) z ≤ E3 (splitAxis T ax).2 x y z) ∧
    (2 ≤ ax → E3 T x y (z/2) ≤ E3 (splitAxis T ax).1 x y z ∧
      E3 T x y ((1+z)/2) ≤ E3 (splitAxis T ax).2 x y z) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · subst h
    simp only [splitAxis, E3_rot]
    rw [← E3_rot T y z (x/2), ← E3_rot T y z ((1+x)/2)]
    exact ⟨E3_splitLast_left _ hy0 hy1 hz0 hz1 hx0 hx1, E3_splitLast_right _ hy0 hy1 hz0 hz1 hx0 hx1⟩
  · subst h
    simp only [splitAxis, E3_rot]
    rw [← E3_rot T (y/2) z x, ← E3_rot (rot T) z x (y/2),
      ← E3_rot T ((1+y)/2) z x, ← E3_rot (rot T) z x ((1+y)/2)]
    exact ⟨E3_splitLast_left _ hz0 hz1 hx0 hx1 hy0 hy1, E3_splitLast_right _ hz0 hz1 hx0 hx1 hy0 hy1⟩
  · obtain ⟨m, rfl⟩ : ∃ m, ax = m+2 := ⟨ax-2, by omega⟩
    simp only [splitAxis]
    exact ⟨E3_splitLast_left _ hx0 hx1 hy0 hy1 hz0 hz1, E3_splitLast_right _ hx0 hx1 hy0 hy1 hz0 hz1⟩

/-! ## Top coefficient -/

lemma foldl_max_ge (l : List ℤ) (init : ℤ) : init ≤ l.foldl max init ∧ ∀ a ∈ l, a ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := ih (max init b)
    refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
    rintro a (rfl | ha)
    · exact le_trans (le_max_right _ _) h1
    · exact h2 a ha

lemma get_le_top (T : Tens) (i j k : ℕ) : T.get i j k ≤ T.top := by
  unfold Tens.get Tens.top
  rw [← Array.foldl_toList]
  obtain ⟨h1, h2⟩ := foldl_max_ge T.data.toList 0
  simp only [Array.getD_eq_getD_getElem?]
  cases h : T.data[T.idx i j k]? with
  | none => simpa using h1
  | some a =>
    simp only [Option.getD_some]
    apply h2
    rw [← Array.getElem?_toList] at h
    exact List.mem_of_getElem? h

lemma top_nonneg (T : Tens) : 0 ≤ T.top := by
  unfold Tens.top
  rw [← Array.foldl_toList]
  exact (foldl_max_ge T.data.toList 0).1

lemma E3_le_top (T : Tens) {x y z : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : E3 T x y z ≤ T.top := by
  rw [E3_eq_e1]
  have hx := sum_B T.n0 x
  have hy := sum_B T.n1 y
  calc ∑ i ∈ range (T.n0+1), ∑ j ∈ range (T.n1+1), B T.n0 i x * B T.n1 j y *
        e1 T.n2 (fun k => (T.get i j k : ℝ)) z
      ≤ ∑ i ∈ range (T.n0+1), ∑ j ∈ range (T.n1+1), B T.n0 i x * B T.n1 j y * (T.top : ℝ) := by
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (B_nonneg _ _ hx0 hx1) (B_nonneg _ _ hy0 hy1))
        exact e1_le _ (fun k _ => by exact_mod_cast get_le_top T i j k) hz0 hz1
    _ = (T.top : ℝ) := by
        rw [show (∑ i ∈ range (T.n0+1), ∑ j ∈ range (T.n1+1), B T.n0 i x * B T.n1 j y * (T.top:ℝ)) =
          (∑ i ∈ range (T.n0+1), B T.n0 i x) * (∑ j ∈ range (T.n1+1), B T.n1 j y) * T.top by
            rw [sum_mul_sum, sum_mul]; exact sum_congr rfl fun i _ => by rw [sum_mul], hx, hy]
        ring

end
end D4Bound.CyclicNative

#print axioms D4Bound.CyclicNative.E3_splitAxis
#print axioms D4Bound.CyclicNative.E3_le_top
