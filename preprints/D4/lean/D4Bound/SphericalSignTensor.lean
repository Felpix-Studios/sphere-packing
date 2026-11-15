import D4Bound.SphericalSignBernstein

/-! Trivariate integer Bernstein upper bounds with closed-domain subdivision.
Every rounding is outward and is justified by an integer inequality. -/
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign.Bernstein
abbrev Tensor := I → I → I → ℤ
noncomputable def ev (p : Tensor) (x y z : ℝ) : ℝ :=
  E (fun i => E (fun j => E (fun k => p i j k) z) y) x

def ceil4096 (a : ℤ) : ℤ := -((-a)/4096)
lemma ceil4096_ge (a : ℤ) : a ≤ 4096*ceil4096 a := by unfold ceil4096; omega

def splitX (right : Bool) (p : Tensor) : Tensor := fun i j k =>
  ceil4096 (∑ h : I, (if right then rcoef i h else lcoef i h)*p h j k)

def swapXY (p : Tensor) : Tensor := fun i j k => p j i k
def swapXZ (p : Tensor) : Tensor := fun i j k => p k j i

def splitY (right : Bool) (p : Tensor) : Tensor := swapXY (splitX right (swapXY p))
def splitZ (right : Bool) (p : Tensor) : Tensor := swapXZ (splitX right (swapXZ p))

lemma ev_mono (p q : Tensor) (h : ∀ i j k, p i j k ≤ q i j k) {x y z : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ev p x y z ≤ ev q x y z := by
  apply E_mono _ hx hx1
  intro i
  apply E_mono _ hy hy1
  intro j
  apply E_mono _ hz hz1
  intro k
  exact_mod_cast h i j k

lemma ev_bound (p : Tensor) (L : ℤ) (h : ∀ i j k, p i j k ≤ L) {x y z : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ev p x y z ≤ L := by
  have hb := ev_mono p (fun _ _ _ => L) h hx hx1 hy hy1 hz hz1
  simpa only [ev,E_const] using hb

lemma E_smul (c : ℝ) (p : I → ℝ) (x : ℝ) : E (fun i => c*p i) x = c*E p x := by
  simp only [E,Finset.mul_sum,mul_assoc]

lemma E_sum (p : I → I → ℝ) (x : ℝ) : E (fun i => ∑ j : I, p j i) x = ∑ j : I, E (p j) x := by
  simp only [E,Finset.sum_mul]
  exact Finset.sum_comm

lemma ev_swapXY (p : Tensor) (x y z : ℝ) : ev (swapXY p) x y z = ev p y x z := by
  simp only [ev,swapXY,E]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma ev_swapXZ (p : Tensor) (x y z : ℝ) : ev (swapXZ p) x y z = ev p z y x := by
  simp only [ev,swapXZ,E]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma ev_splitX (right : Bool) (p : Tensor) {x y z : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ev p (if right then (x+1)/2 else x/2) y z ≤ ev (splitX right p) x y z := by
  let c : I → I → ℤ := if right then rcoef else lcoef
  have hc : ∀ i j k, ((∑ h : I, c i h*p h j k : ℤ) : ℝ) ≤
      4096*(splitX right p i j k : ℝ) := by
    intro i j k
    have hh : (∑ h : I, c i h*p h j k) ≤ 4096*splitX right p i j k := by
      cases right <;> simpa [c,splitX] using ceil4096_ge (∑ h : I, c i h*p h j k)
    exact_mod_cast hh
  have hm : E (fun i => E (fun j => E (fun k => ((∑ h : I,c i h*p h j k : ℤ) : ℝ)) z) y) x ≤
      E (fun i => E (fun j => E (fun k => 4096*(splitX right p i j k : ℝ)) z) y) x := by
    apply E_mono _ hx hx1
    intro i
    apply E_mono _ hy hy1
    intro j
    apply E_mono _ hz hz1
    exact hc i j
  simp only [Int.cast_sum,Int.cast_mul] at hm
  simp_rw [E_sum,E_smul] at hm
  have he : E (fun i => ∑ h : I, (c i h : ℝ)*E (fun j => E (fun k => (p h j k : ℝ)) z) y) x =
      4096*ev p (if right then (x+1)/2 else x/2) y z := by
    cases right
    · exact E_left _ x
    · exact E_right _ x
  rw [← E_sum,he] at hm
  change 4096 * ev p _ y z ≤ 4096 * ev (splitX right p) x y z at hm
  linarith

lemma ev_splitY (right : Bool) (p : Tensor) {x y z : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ev p x (if right then (y+1)/2 else y/2) z ≤ ev (splitY right p) x y z := by
  simpa only [splitY,ev_swapXY] using ev_splitX right (swapXY p) hy hy1 hx hx1 hz hz1

lemma ev_splitZ (right : Bool) (p : Tensor) {x y z : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ev p x y (if right then (z+1)/2 else z/2) ≤ ev (splitZ right p) x y z := by
  simpa only [splitZ,ev_swapXZ] using ev_splitX right (swapXZ p) hz hz1 hy hy1 hx hx1

lemma E_add (p q : I → ℝ) (x : ℝ) : E (fun i => p i+q i) x = E p x+E q x := by
  simp only [E,add_mul,Finset.sum_add_distrib]

noncomputable def Good (p d : Tensor) (x y z : ℝ) : Prop := ev d x y z < 0 ∨ ev p x y z ≤ 0

def combine (v u : ℕ) (p d : Tensor) : Tensor := fun i j k => (v:ℤ)*p i j k+(u:ℤ)*d i j k
lemma ev_combine (v u : ℕ) (p d : Tensor) (x y z : ℝ) :
    ev (combine v u p d) x y z = (v:ℝ)*ev p x y z+(u:ℝ)*ev d x y z := by
  simp only [ev,combine,Int.cast_add,Int.cast_mul,Int.cast_natCast,E_add,E_smul]

/-- This implication is the reason nonnegative Gram multipliers may compress
an existing subdivision certificate without weakening its domain. -/
lemma gram_multiplier (P D : ℝ) (v u : ℕ) (hv : 0<v)
    (h : (v:ℝ)*P+(u:ℝ)*D ≤ 0) : D<0 ∨ P≤0 := by
  by_cases hd : D<0
  · exact Or.inl hd
  · right
    have hd0 : 0 ≤ D := le_of_not_gt hd
    have hu : 0 ≤ (u:ℝ)*D := mul_nonneg (Nat.cast_nonneg _) hd0
    have hvR : (0:ℝ)<v := by exact_mod_cast hv
    exact nonpos_of_mul_nonpos_right (show (v:ℝ)*P≤0 by linarith) hvR

lemma multiplier_sound (p d : Tensor) (v u : ℕ) (hv : 0<v)
    (h : ∀ i j k, combine v u p d i j k ≤ 0) {x y z : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Good p d x y z := by
  have hb := ev_bound (combine v u p d) 0 h hx hx1 hy hy1 hz hz1
  rw [ev_combine] at hb
  exact gram_multiplier _ _ v u hv (by simpa using hb)

lemma excluded_sound (p d : Tensor) (h : ∀ i j k, d i j k ≤ -1) {x y z : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Good p d x y z := by
  have hb := ev_bound d (-1) h hx hx1 hy hy1 hz hz1
  exact Or.inl (by norm_num at hb; linarith)

end D4Bound.SphericalSign.Bernstein
