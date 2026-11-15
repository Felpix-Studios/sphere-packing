import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

/-!
# Bernstein identities for the native cyclic checker

Real-valued facts used by `CyclicNativeSound`: the Bernstein basis sums to one,
the power-to-Bernstein transform, and the exact midpoint de Casteljau
subdivision identities for both halves, for every degree.
-/
namespace D4Bound.CyclicNative
open Finset

noncomputable section

/-- Bernstein basis polynomial. -/
def B (n i : ℕ) (x : ℝ) : ℝ := (n.choose i : ℝ) * x^i * (1-x)^(n-i)

lemma B_nonneg (n i : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ B n i x := by
  have : 0 ≤ 1 - x := by linarith
  unfold B; positivity

lemma sum_B (n : ℕ) (x : ℝ) : ∑ i ∈ range (n+1), B n i x = 1 := by
  have h := add_pow x (1-x) n
  rw [show x + (1-x) = 1 by ring, one_pow] at h
  rw [h]
  apply sum_congr rfl
  intro i _
  unfold B; ring

/-- Univariate Bernstein form. -/
def e1 (n : ℕ) (g : ℕ → ℝ) (x : ℝ) : ℝ := ∑ i ∈ range (n+1), g i * B n i x

lemma e1_mono (n : ℕ) {g h : ℕ → ℝ} (hgh : ∀ i ≤ n, g i ≤ h i) {x : ℝ}
    (h0 : 0 ≤ x) (h1 : x ≤ 1) : e1 n g x ≤ e1 n h x := by
  apply sum_le_sum
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  exact mul_le_mul_of_nonneg_right (hgh i hi') (B_nonneg n i h0 h1)

lemma e1_le (n : ℕ) {g : ℕ → ℝ} {M : ℝ} (hg : ∀ i ≤ n, g i ≤ M) {x : ℝ}
    (h0 : 0 ≤ x) (h1 : x ≤ 1) : e1 n g x ≤ M := by
  have := e1_mono n hg h0 h1
  have hc : e1 n (fun _ => M) x = M := by
    unfold e1; rw [← mul_sum, sum_B, mul_one]
  linarith

/-- Truncation of an indicator sum below `i`. -/
lemma sum_trunc_le (F : ℕ → ℝ) {i n : ℕ} (h : i ≤ n) :
    ∑ l ∈ range (n+1), (if l ≤ i then F l else 0) = ∑ l ∈ range (i+1), F l := by
  rw [← sum_range_add_sum_Ico _ (show i+1 ≤ n+1 by omega)]
  have h1 : ∑ l ∈ range (i+1), (if l ≤ i then F l else 0) = ∑ l ∈ range (i+1), F l := by
    apply sum_congr rfl
    intro l hl
    rw [if_pos (Nat.lt_succ_iff.mp (mem_range.mp hl))]
  have h2 : ∑ l ∈ Ico (i+1) (n+1), (if l ≤ i then F l else 0) = 0 := by
    apply sum_eq_zero
    intro l hl
    rw [if_neg (by have := (mem_Ico.mp hl).1; omega)]
  rw [h1, h2, add_zero]

/-- Truncation of an indicator sum above `i`, shifted to start at zero. -/
lemma sum_trunc_ge (F : ℕ → ℝ) {i n : ℕ} (h : i ≤ n) :
    ∑ l ∈ range (n+1), (if i ≤ l then F l else 0) = ∑ m ∈ range (n-i+1), F (i+m) := by
  rw [← sum_range_add_sum_Ico _ (show i ≤ n+1 by omega)]
  have h1 : ∑ l ∈ range i, (if i ≤ l then F l else 0) = 0 := by
    apply sum_eq_zero
    intro l hl
    rw [if_neg (by have := mem_range.mp hl; omega)]
  have h2 : ∑ l ∈ Ico i (n+1), (if i ≤ l then F l else 0) = ∑ l ∈ Ico i (n+1), F l := by
    apply sum_congr rfl
    intro l hl
    rw [if_pos (mem_Ico.mp hl).1]
  rw [h1, h2, zero_add, sum_Ico_eq_sum_range, show n+1-i = n-i+1 by omega]

/-- `y^l (y+z)^(n-l)` in the basis `y^i z^(n-i)`. -/
lemma expand_left (n l : ℕ) (hl : l ≤ n) (y z : ℝ) :
    y^l*(y+z)^(n-l) = ∑ i ∈ range (n+1),
      (if l ≤ i then ((n-l).choose (i-l) : ℝ)*y^i*z^(n-i) else 0) := by
  rw [sum_trunc_ge (fun i => ((n-l).choose (i-l) : ℝ)*y^i*z^(n-i)) hl, add_pow, mul_sum]
  apply sum_congr rfl
  intro m hm
  have hm' : m ≤ n-l := Nat.lt_succ_iff.mp (mem_range.mp hm)
  simp only [show l+m-l = m by omega, show n-(l+m) = n-l-m by omega, pow_add]
  ring

/-- `(y+z)^l z^(n-l)` in the basis `y^i z^(n-i)`. -/
lemma expand_right (n l : ℕ) (hl : l ≤ n) (y z : ℝ) :
    (y+z)^l*z^(n-l) = ∑ i ∈ range (n+1),
      (if i ≤ l then (l.choose i : ℝ)*y^i*z^(n-i) else 0) := by
  rw [sum_trunc_le (fun i => (l.choose i : ℝ)*y^i*z^(n-i)) hl, add_pow, sum_mul]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ l := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have : n-i = (l-i)+(n-l) := by omega
  rw [this, pow_add]
  ring

/-- Power basis to scaled Bernstein basis, for every degree bound `n`. -/
lemma power_to_bernstein (n : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    ∑ l ∈ range (n+1), a l * x^l =
      ∑ i ∈ range (n+1), (∑ l ∈ range (i+1), ((n-l).choose (i-l) : ℝ) * a l) *
        (x^i*(1-x)^(n-i)) := by
  have hx : ∀ l ∈ range (n+1), a l * x^l = ∑ i ∈ range (n+1),
      (if l ≤ i then ((n-l).choose (i-l) : ℝ) * a l * (x^i*(1-x)^(n-i)) else 0) := by
    intro l hl
    have hl' : l ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hl)
    have e := expand_left n l hl' x (1-x)
    rw [show x + (1-x) = 1 by ring, one_pow, mul_one] at e
    rw [e, mul_sum]
    apply sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [sum_congr rfl hx, sum_comm]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [sum_trunc_le (fun l => ((n-l).choose (i-l) : ℝ) * a l * (x^i*(1-x)^(n-i))) hi', sum_mul]

/-! ## Exact de Casteljau triangle -/

def triR (g : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, i => g i
  | l+1, i => (triR g l i + triR g l (i+1))/2

lemma triR_closed (g : ℕ → ℝ) (l : ℕ) : ∀ i, triR g l i =
    (1/2)^l * ∑ m ∈ range (l+1), (l.choose m : ℝ) * g (i+m) := by
  induction l with
  | zero => intro i; simp [triR]
  | succ l ih =>
    intro i
    rw [triR, ih i, ih (i+1)]
    have key : ∑ m ∈ range (l+1+1), ((l+1).choose m : ℝ) * g (i+m) =
        ∑ m ∈ range (l+1), (l.choose m : ℝ) * g (i+m) +
        ∑ m ∈ range (l+1), (l.choose m : ℝ) * g (i+1+m) := by
      rw [sum_range_succ', sum_range_succ' (fun m => (l.choose m : ℝ) * g (i+m))]
      have hs : ∀ m ∈ range (l+1), ((l+1).choose (m+1) : ℝ) * g (i+(m+1)) =
          (l.choose m : ℝ) * g (i+1+m) + (l.choose (m+1) : ℝ) * g (i+(m+1)) := by
        intro m _
        rw [Nat.choose_succ_succ', Nat.cast_add, show i+1+m = i+(m+1) by ring]
        ring
      rw [sum_congr rfl hs, sum_add_distrib, sum_range_succ (fun m => (l.choose (m+1) : ℝ) * g (i+(m+1))),
        Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
      simp only [Nat.choose_zero_right]
      ring
    rw [key, pow_succ]
    ring

/-- Left half: `e1 g (x/2) = e1 (left) x`. -/
lemma e1_left (n : ℕ) (g : ℕ → ℝ) (x : ℝ) :
    e1 n g (x/2) = e1 n (fun i => triR g i 0) x := by
  unfold e1 B
  have hx : ∀ l ∈ range (n+1), g l * ((n.choose l : ℝ) * (x/2)^l * (1-x/2)^(n-l)) =
      ∑ i ∈ range (n+1), (if l ≤ i then
        g l * (n.choose l : ℝ) * ((n-l).choose (i-l) : ℝ) * (1/2)^i * (x^i*(1-x)^(n-i)) else 0) := by
    intro l hl
    have hl' : l ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hl)
    have e := expand_left n l hl' (x/2) (1-x)
    rw [show x/2 + (1-x) = 1-x/2 by ring] at e
    rw [show g l * ((n.choose l : ℝ) * (x/2)^l * (1-x/2)^(n-l)) =
      g l * (n.choose l : ℝ) * ((x/2)^l * (1-x/2)^(n-l)) by ring, e, mul_sum]
    apply sum_congr rfl
    intro i _
    split_ifs
    · simp only [div_pow, one_div, inv_pow]; ring
    · ring
  rw [sum_congr rfl hx, sum_comm]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [sum_trunc_le (fun l => g l * (n.choose l : ℝ) * ((n-l).choose (i-l) : ℝ) * (1/2)^i *
    (x^i*(1-x)^(n-i))) hi'] 
  dsimp only
  rw [triR_closed, mul_sum, sum_mul]
  apply sum_congr rfl
  intro l hl
  have hl' : l ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hl)
  have hc : (n.choose l : ℝ) * ((n-l).choose (i-l) : ℝ) = (n.choose i : ℝ) * (i.choose l : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := n) hl').symm
  simp only [zero_add]
  linear_combination (g l * (1/2)^i * x^i * (1-x)^(n-i)) * hc

/-- Right half: `e1 g ((1+x)/2) = e1 (right) x`. -/
lemma e1_right (n : ℕ) (g : ℕ → ℝ) (x : ℝ) :
    e1 n g ((1+x)/2) = e1 n (fun i => triR g (n-i) i) x := by
  unfold e1 B
  have hx : ∀ l ∈ range (n+1), g l * ((n.choose l : ℝ) * ((1+x)/2)^l * (1-(1+x)/2)^(n-l)) =
      ∑ i ∈ range (n+1), (if i ≤ l then
        g l * (n.choose l : ℝ) * (l.choose i : ℝ) * (1/2)^(n-i) * (x^i*(1-x)^(n-i)) else 0) := by
    intro l hl
    have hl' : l ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hl)
    have e := expand_right n l hl' x ((1-x)/2)
    rw [show x + (1-x)/2 = (1+x)/2 by ring] at e
    rw [show g l * ((n.choose l : ℝ) * ((1+x)/2)^l * (1-(1+x)/2)^(n-l)) =
      g l * (n.choose l : ℝ) * (((1+x)/2)^l * ((1-x)/2)^(n-l)) by ring, e, mul_sum]
    apply sum_congr rfl
    intro i _
    split_ifs
    · simp only [div_pow, one_div, inv_pow]; ring
    · ring
  rw [sum_congr rfl hx, sum_comm]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [sum_trunc_ge (fun l => g l * (n.choose l : ℝ) * (l.choose i : ℝ) * (1/2)^(n-i) *
    (x^i*(1-x)^(n-i))) hi'] 
  dsimp only
  rw [triR_closed, mul_sum, sum_mul]
  apply sum_congr rfl
  intro m hm
  have hm' : m ≤ n-i := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hc : (n.choose (i+m) : ℝ) * ((i+m).choose i : ℝ) = (n.choose i : ℝ) * ((n-i).choose m : ℝ) := by
    have := Nat.choose_mul (n := n) (k := i+m) (s := i) (by omega)
    rw [show i+m-i = m by omega] at this
    exact_mod_cast this
  linear_combination (g (i+m) * (1/2)^(n-i) * x^i * (1-x)^(n-i)) * hc

end
end D4Bound.CyclicNative

#print axioms D4Bound.CyclicNative.e1_left
#print axioms D4Bound.CyclicNative.e1_right
#print axioms D4Bound.CyclicNative.power_to_bernstein
