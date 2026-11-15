import D4Bound.KernelBoxNativeModel

/-!
# Node lower polynomials and the self-subdividing kernel-box checker

On a box of the `(u, v, t) = (r - 1, s - 1, t)` coordinates, the positive corrections of
`-V7.pair` (caps, tents, allocations, graphs) are replaced by polynomial lower bounds whose
branch is decided on the box. Together with `baseP` this gives a polynomial that bounds
`-pair r s t - λ q(t)` from below on the box. `search` bisects boxes until the centred
lower bound `low3` of that polynomial is nonnegative. `search_sound` and `checkCell_sound`
prove that a `true` answer implies the kernel inequality on the whole cell pair.
-/

namespace D4Bound.KBN
open V7

structure Box where
  cu : ℚ
  cv : ℚ
  ct : ℚ
  hu : ℚ
  hv : ℚ
  ht : ℚ

def Box.Mem (b : Box) (u v t : ℝ) : Prop :=
  |u - b.cu| ≤ b.hu ∧ |v - b.cv| ≤ b.hv ∧ |t - b.ct| ≤ b.ht

def lowOn (b : Box) (p : P3) : ℚ := low3 b.hu b.hv b.ht (shift3 b.cu b.cv b.ct p)

theorem lowOn_sound {b : Box} {u v t : ℝ} (hm : b.Mem u v t) (p : P3) :
    (lowOn b p : ℝ) ≤ E3 p u v t := by
  have := low3_sound hm.1 hm.2.1 hm.2.2 (shift3 b.cu b.cv b.ct p)
  rw [E3_shift3] at this
  simp only [add_sub_cancel] at this
  exact this

def nonneg (b : Box) (p : P3) : Bool := decide (0 ≤ lowOn b p)
def pos (b : Box) (p : P3) : Bool := decide (0 < lowOn b p)

theorem nonneg_sound {b : Box} {p : P3} (h : nonneg b p = true) {u v t : ℝ}
    (hm : b.Mem u v t) : 0 ≤ E3 p u v t := by
  have h0 : (0 : ℝ) ≤ (lowOn b p : ℝ) := by exact_mod_cast (decide_eq_true_eq.mp h)
  linarith [lowOn_sound hm p]

theorem pos_sound {b : Box} {p : P3} (h : pos b p = true) {u v t : ℝ}
    (hm : b.Mem u v t) : 0 < E3 p u v t := by
  have h0 : (0 : ℝ) < (lowOn b p : ℝ) := by exact_mod_cast (decide_eq_true_eq.mp h)
  linarith [lowOn_sound hm p]

/-- Rational value at the box centre (used only to choose a branch). -/
def ev1 (p : P1) (x : ℚ) : ℚ := p.foldr (fun a acc => a + x * acc) 0
def ev2 (p : P2) (y z : ℚ) : ℚ := p.foldr (fun a acc => ev1 a z + y * acc) 0
def ev3 (p : P3) (x y z : ℚ) : ℚ := p.foldr (fun a acc => ev2 a y z + x * acc) 0
def centre (b : Box) (p : P3) : ℚ := ev3 p b.cu b.cv b.ct

/-! ## Variable selectors -/

def liftX (sd : Bool) (p : P1) : P3 := if sd then liftV p else liftU p

theorem E3_liftX (sd : Bool) (p : P1) (r s t : ℝ) :
    E3 (liftX sd p) (r - 1) (s - 1) t = E1 p ((if sd then s else r) - 1) := by
  cases sd <;> simp [liftX, E3_liftU, E3_liftV]

theorem E1_quad (x : ℝ) : E1 [1, 2, 1] (x - 1) = x * x := by
  simp only [E1, peval_cons, peval_nil]; push_cast; ring
theorem E1_lin (x : ℝ) : E1 [1, 1] (x - 1) = x := by
  simp only [E1, peval_cons, peval_nil]; push_cast; ring
theorem E1_T (t : ℝ) : E1 [0, 1] t = t := by
  simp only [E1, peval_cons, peval_nil]; push_cast; ring

/-! ## Caps -/

def capL (c : Cap) (sd : Bool) : P3 :=
  A3.add (liftX sd [1 + c.d ^ 2 - c.a2, 2, 1])
    (A3.smul (-2 * c.d * c.sigma) (A3.mul (liftX sd [1, 1]) (liftT [0, 1])))

def capK (c : Cap) (sd : Bool) : P3 :=
  A3.smul (4 * c.d ^ 2 * (1 - c.sigma ^ 2)) (A3.mul (liftX sd [1, 2, 1]) (liftT [1, 0, -1]))

def capLL (c : Cap) (sd : Bool) : P3 := A3.mul (capL c sd) (capL c sd)

/-- `sd` selects the variable `x` of a lift. -/
def XSel (sd : Bool) (r s t x : ℝ) : Prop :=
  ∀ p : P1, E3 (liftX sd p) (r - 1) (s - 1) t = E1 p (x - 1)

theorem xsel_false (r s t : ℝ) : XSel false r s t r := fun p => by simp [liftX, E3_liftU]
theorem xsel_true (r s t : ℝ) : XSel true r s t s := fun p => by simp [liftX, E3_liftV]

/-- `L = 2 d x A`, the numerator of the cap angle variable. -/
noncomputable def capLr (c : Cap) (x t : ℝ) : ℝ :=
  x * x + (c.d : ℝ) ^ 2 - c.a2 - 2 * c.d * c.sigma * x * t

/-- `K = (2 d x)² S`. -/
noncomputable def capKr (c : Cap) (x t : ℝ) : ℝ :=
  4 * (c.d : ℝ) ^ 2 * x ^ 2 * ((1 - (c.sigma : ℝ) ^ 2) * (1 - t * t))

theorem E3_capL {c : Cap} {sd : Bool} {r s t x : ℝ} (hx : XSel sd r s t x) :
    E3 (capL c sd) (r - 1) (s - 1) t = capLr c x t := by
  unfold XSel at hx
  unfold capLr
  simp only [capL, E3_add, E3_smul, E3_mul, hx, E3_liftT, E1_T]
  have h1 : E1 [1 + c.d ^ 2 - c.a2, 2, 1] (x - 1) = x * x + (c.d : ℝ) ^ 2 - c.a2 := by
    simp only [E1, peval_cons, peval_nil]; push_cast; ring
  rw [h1, E1_lin]
  push_cast; ring

theorem E3_capK {c : Cap} {sd : Bool} {r s t x : ℝ} (hx : XSel sd r s t x) :
    E3 (capK c sd) (r - 1) (s - 1) t = capKr c x t := by
  unfold XSel at hx
  unfold capKr
  simp only [capK, E3_smul, E3_mul, hx, E3_liftT, E1_quad]
  have : E1 [1, 0, -1] t = 1 - t * t := by
    simp only [E1, peval_cons, peval_nil]; push_cast; ring
  rw [this]
  push_cast; ring

theorem E3_capLL {c : Cap} {sd : Bool} {r s t x : ℝ} (hx : XSel sd r s t x) :
    E3 (capLL c sd) (r - 1) (s - 1) t = capLr c x t ^ 2 := by
  simp only [capLL, E3_mul, E3_capL hx]; ring

/-- Shared facts about the cap angle variable. -/
theorem cap_basics {c : Cap} (hc : CapValid c) {x t : ℝ} (hx : 0 < x) (ht1 : -1 ≤ t)
    (ht2 : t ≤ 1) :
    0 < 2 * (c.d : ℝ) * x ∧
    ((x * x + (c.d : ℝ) ^ 2 - c.a2) / (2 * c.d * x) - c.sigma * t) * (2 * c.d * x) = capLr c x t ∧
    0 ≤ (1 - (c.sigma : ℝ) ^ 2) * (1 - t * t) ∧
    capKr c x t = (2 * (c.d : ℝ) * x) ^ 2 * ((1 - (c.sigma : ℝ) ^ 2) * (1 - t * t)) := by
  have hd : (0 : ℝ) < c.d := by exact_mod_cast hc.1
  have hs1 : (-1 : ℝ) ≤ c.sigma := by exact_mod_cast hc.2.2.1
  have hs2 : (c.sigma : ℝ) ≤ 1 := by exact_mod_cast hc.2.2.2.1
  have h2 : 0 < 2 * (c.d : ℝ) * x := by positivity
  refine ⟨h2, ?_, ?_, ?_⟩
  · unfold capLr; rw [sub_mul, div_mul_cancel₀ _ h2.ne']; ring
  · apply mul_nonneg <;> nlinarith
  · unfold capKr; ring

/-- Lower level `(1+e)/2` on the `A ≤ 0` side. -/
theorem capProbability_geA {c : Cap} (hc : CapValid c) {x t : ℝ} (hx : 0 < x)
    (ht1 : -1 ≤ t) (ht2 : t ≤ 1) (hL : capLr c x t ≤ 0) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hG : c.sigma ^ 2 = 1 ∨ 0 ≤ capLr c x t ^ 2 - e ^ 2 * capKr c x t) :
    (1 + e) / 2 ≤ capProbability c x t := by
  obtain ⟨h2, hAe, hS0, hK⟩ := cap_basics hc hx ht1 ht2
  have hA : (x * x + (c.d : ℝ) ^ 2 - c.a2) / (2 * c.d * x) - c.sigma * t ≤ 0 := by
    by_contra hneg
    have := mul_pos (lt_of_not_ge hneg) h2
    linarith
  unfold capProbability
  dsimp only
  by_cases hS : (1 - (c.sigma : ℝ) ^ 2) * (1 - t * t) = 0
  · rw [if_pos hS, if_pos hA]; linarith
  · rw [if_neg hS]
    set A := (x * x + (c.d : ℝ) ^ 2 - c.a2) / (2 * c.d * x) - c.sigma * t with hAdef
    set S := (1 - (c.sigma : ℝ) ^ 2) * (1 - t * t) with hSdef
    have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
    have hG' : e ^ 2 * ((2 * (c.d : ℝ) * x) ^ 2 * S) ≤ (A * (2 * c.d * x)) ^ 2 := by
      rw [hAe, ← hK]
      rcases hG with hG | hG
      · exfalso
        have : (1 - (c.sigma : ℝ) ^ 2) = 0 := by
          have : ((c.sigma ^ 2 : ℚ) : ℝ) = 1 := by exact_mod_cast hG
          push_cast at this; linarith
        apply hS; rw [hSdef, this, zero_mul]
      · linarith
    have hAsq : (e * Real.sqrt S) ^ 2 ≤ A ^ 2 := by
      have hpos : 0 < (2 * (c.d : ℝ) * x) ^ 2 := by positivity
      rw [mul_pow, Real.sq_sqrt hS0]
      have : e ^ 2 * S * (2 * (c.d : ℝ) * x) ^ 2 ≤ A ^ 2 * (2 * (c.d : ℝ) * x) ^ 2 := by
        nlinarith [hG']
      exact le_of_mul_le_mul_right this hpos
    have hs := Real.sqrt_pos.mpr hSpos
    have hsq : e * Real.sqrt S ≤ -A := by
      have := sq_le_sq.mp hAsq
      rw [abs_of_nonneg (by positivity), abs_of_nonpos hA] at this
      linarith [le_abs_self (e * Real.sqrt S)]
    have h1 : (1 + e) / 2 ≤ (1 - A / Real.sqrt S) / 2 := by
      have : A / Real.sqrt S ≤ -e := by
        rw [div_le_iff₀ hs]; linarith
      linarith
    exact le_max_of_le_right (le_min (by linarith) h1)

/-- Lower level `(1-e)/2` when `|A| ≤ e √S`. -/
theorem capProbability_geB {c : Cap} (hc : CapValid c) {x t : ℝ} (hx : 0 < x)
    (ht1 : -1 ≤ t) (ht2 : t ≤ 1) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hH : 0 ≤ e ^ 2 * capKr c x t - capLr c x t ^ 2) :
    (1 - e) / 2 ≤ capProbability c x t := by
  obtain ⟨h2, hAe, hS0, hK⟩ := cap_basics hc hx ht1 ht2
  unfold capProbability
  dsimp only
  by_cases hS : (1 - (c.sigma : ℝ) ^ 2) * (1 - t * t) = 0
  · rw [if_pos hS]
    have hL0 : capLr c x t = 0 := by
      rw [hK, hS, mul_zero, mul_zero] at hH
      nlinarith [sq_nonneg (capLr c x t)]
    have hA : (x * x + (c.d : ℝ) ^ 2 - c.a2) / (2 * c.d * x) - c.sigma * t ≤ 0 := by
      have : ((x * x + (c.d : ℝ) ^ 2 - c.a2) / (2 * c.d * x) - c.sigma * t) * (2 * c.d * x) = 0 := by
        rw [hAe, hL0]
      rcases mul_eq_zero.mp this with h | h
      · rw [h]
      · linarith
    rw [if_pos hA]; linarith
  · rw [if_neg hS]
    set A := (x * x + (c.d : ℝ) ^ 2 - c.a2) / (2 * c.d * x) - c.sigma * t with hAdef
    set S := (1 - (c.sigma : ℝ) ^ 2) * (1 - t * t) with hSdef
    have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
    have hAsq : A ^ 2 ≤ (e * Real.sqrt S) ^ 2 := by
      have hpos : 0 < (2 * (c.d : ℝ) * x) ^ 2 := by positivity
      rw [mul_pow, Real.sq_sqrt hS0]
      have h' : (A * (2 * c.d * x)) ^ 2 ≤ e ^ 2 * ((2 * (c.d : ℝ) * x) ^ 2 * S) := by
        rw [hAe, ← hK]; linarith
      have : A ^ 2 * (2 * (c.d : ℝ) * x) ^ 2 ≤ e ^ 2 * S * (2 * (c.d : ℝ) * x) ^ 2 := by
        nlinarith [h']
      exact le_of_mul_le_mul_right this hpos
    have hs := Real.sqrt_pos.mpr hSpos
    have hsq : A ≤ e * Real.sqrt S := by
      have := sq_le_sq.mp hAsq
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ e * Real.sqrt S)] at this
      exact le_trans (le_abs_self A) this
    have h1 : (1 - e) / 2 ≤ (1 - A / Real.sqrt S) / 2 := by
      have : A / Real.sqrt S ≤ e := by
        rw [div_le_iff₀ hs]; linarith
      linarith
    exact le_max_of_le_right (le_min (by linarith) h1)

/-- Caps that may be decided at all: positive weight above a threshold, nonzero cut factor. -/
def capActive (k : ℕ) (c : Cap) : Bool :=
  decide (1 / 10 ^ 13 ≤ c.weight) && decide (capCut k c ≠ 0)

def levelA (b : Box) (c : Cap) (sd : Bool) : List ℚ → ℚ
  | [] => 0
  | e :: L =>
    if decide (0 ≤ e ∧ e ≤ 1) && (decide (c.sigma ^ 2 = 1) ||
        nonneg b (A3.add (capLL c sd) (A3.smul (-(e ^ 2)) (capK c sd)))) then (1 + e) / 2
    else levelA b c sd L

def levelB (b : Box) (c : Cap) (sd : Bool) : List ℚ → ℚ
  | [] => 0
  | e :: L =>
    if decide (0 ≤ e ∧ e ≤ 1) &&
        nonneg b (A3.add (A3.smul (e ^ 2) (capK c sd)) (A3.smul (-1) (capLL c sd))) then (1 - e) / 2
    else levelB b c sd L

/-- A certified constant lower bound of the cap probability on the box. -/
def capLevel (b : Box) (c : Cap) (sd : Bool) : ℚ :=
  if nonneg b (A3.smul (-1) (capL c sd)) then levelA b c sd [1, 3 / 4, 1 / 2, 1 / 4, 0]
  else if c.sigma ^ 2 = 1 then 0 else levelB b c sd [1 / 4, 1 / 2, 3 / 4]

theorem levelA_sound {b : Box} {c : Cap} (hc : CapValid c) {sd : Bool} {r s t x : ℝ}
    (hx : XSel sd r s t x) (hx0 : 0 < x) (hm : b.Mem (r - 1) (s - 1) t) (ht1 : -1 ≤ t)
    (ht2 : t ≤ 1) (hL : capLr c x t ≤ 0) :
    ∀ L : List ℚ, 0 ≤ levelA b c sd L ∧ (levelA b c sd L : ℝ) ≤ capProbability c x t
  | [] => ⟨le_rfl, by simpa [levelA] using capProbability_nonneg c x t⟩
  | e :: L => by
    unfold levelA
    by_cases hsel : (decide (0 ≤ e ∧ e ≤ 1) && (decide (c.sigma ^ 2 = 1) ||
        nonneg b (A3.add (capLL c sd) (A3.smul (-(e ^ 2)) (capK c sd))))) = true
    · rw [if_pos hsel]
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hsel
      obtain ⟨⟨he0, he1⟩, hG⟩ := hsel
      refine ⟨by linarith, ?_⟩
      have := capProbability_geA hc hx0 ht1 ht2 hL (e := (e : ℝ)) (by exact_mod_cast he0)
        (by exact_mod_cast he1) (by
          rcases hG with hG | hG
          · exact Or.inl hG
          · have h := nonneg_sound hG hm
            rw [E3_add, E3_smul, E3_capLL hx, E3_capK hx] at h
            push_cast at h
            exact Or.inr (by linarith))
      push_cast; linarith
    · rw [if_neg hsel]
      exact levelA_sound hc hx hx0 hm ht1 ht2 hL L

theorem levelB_sound {b : Box} {c : Cap} (hc : CapValid c) {sd : Bool} {r s t x : ℝ}
    (hx : XSel sd r s t x) (hx0 : 0 < x) (hm : b.Mem (r - 1) (s - 1) t) (ht1 : -1 ≤ t)
    (ht2 : t ≤ 1) :
    ∀ L : List ℚ, 0 ≤ levelB b c sd L ∧ (levelB b c sd L : ℝ) ≤ capProbability c x t
  | [] => ⟨le_rfl, by simpa [levelB] using capProbability_nonneg c x t⟩
  | e :: L => by
    unfold levelB
    by_cases hsel : (decide (0 ≤ e ∧ e ≤ 1) &&
        nonneg b (A3.add (A3.smul (e ^ 2) (capK c sd)) (A3.smul (-1) (capLL c sd)))) = true
    · rw [if_pos hsel]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsel
      obtain ⟨⟨he0, he1⟩, hH⟩ := hsel
      refine ⟨by linarith, ?_⟩
      have h := nonneg_sound hH hm
      rw [E3_add, E3_smul, E3_smul, E3_capLL hx, E3_capK hx] at h
      push_cast at h
      have := capProbability_geB hc hx0 ht1 ht2 (e := (e : ℝ)) (by exact_mod_cast he0)
        (by exact_mod_cast he1) (by linarith)
      push_cast; linarith
    · rw [if_neg hsel]
      exact levelB_sound hc hx hx0 hm ht1 ht2 L

theorem capLevel_sound {b : Box} {c : Cap} (hc : CapValid c) {sd : Bool} {r s t x : ℝ}
    (hx : XSel sd r s t x) (hx0 : 0 < x) (hm : b.Mem (r - 1) (s - 1) t) (ht1 : -1 ≤ t)
    (ht2 : t ≤ 1) : 0 ≤ capLevel b c sd ∧ (capLevel b c sd : ℝ) ≤ capProbability c x t := by
  unfold capLevel
  by_cases hL : nonneg b (A3.smul (-1) (capL c sd)) = true
  · rw [if_pos hL]
    have h := nonneg_sound hL hm
    rw [E3_smul, E3_capL hx] at h
    push_cast at h
    exact levelA_sound hc hx hx0 hm ht1 ht2 (by linarith) _
  · rw [if_neg hL]
    by_cases hs : c.sigma ^ 2 = 1
    · rw [if_pos hs]; exact ⟨le_rfl, by simpa using capProbability_nonneg c x t⟩
    · rw [if_neg hs]; exact levelB_sound hc hx hx0 hm ht1 ht2 _

/-- Lower polynomial of `w/2 · capWeight c y · capProbability c x t`, `x` selected by `sd`
and `y` the other radius, lying in cell `ky`. -/
def capTerm (ky : ℕ) (b : Box) (c : Cap) (sd : Bool) : P3 :=
  if capActive ky c then
    A3.smul (c.weight / 2 * capCut ky c * capLevel b c sd) (liftX (!sd) (rvP c.vector ky))
  else A3.zero

def capsLow (kr ks : ℕ) (b : Box) : P3 :=
  psum A2 (caps.map fun c => A3.add (capTerm ks b c false) (capTerm kr b c true))

/-- Common hypotheses at a node. -/
structure NodeHyp (kr ks : ℕ) (b : Box) (r s t : ℝ) : Prop where
  cp : CellPair kr ks r s
  cr : capsCutOK kr = true
  cs : capsCutOK ks = true
  mem : b.Mem (r - 1) (s - 1) t
  t1 : -1 ≤ t
  t2 : t ≤ 1

theorem NodeHyp.range_r {kr ks : ℕ} {b : Box} {r s t : ℝ} (h : NodeHyp kr ks b r s t) :
    1 ≤ r ∧ r ≤ 7 / 4 := cell_range h.cp.hr h.cp.kr7
theorem NodeHyp.range_s {kr ks : ℕ} {b : Box} {r s t : ℝ} (h : NodeHyp kr ks b r s t) :
    1 ≤ s ∧ s ≤ 7 / 4 := cell_range h.cp.hs h.cp.ks7

theorem capTerm_core {ky : ℕ} {b : Box} {r s t x y : ℝ} {c : Cap} (hc : c ∈ caps)
    (sd : Bool) (hx : XSel sd r s t x) (hy : XSel (!sd) r s t y) (hyc : CellOne ky y)
    (hx0 : 0 < x) (hm : b.Mem (r - 1) (s - 1) t) (ht1 : -1 ≤ t) (ht2 : t ≤ 1) :
    E3 (capTerm ky b c sd) (r - 1) (s - 1) t ≤
      (c.weight : ℝ) * capWeight c y * capProbability c x t / 2 := by
  have hv := caps_data_valid c hc
  have hw : (0 : ℝ) ≤ c.weight := by exact_mod_cast hv.2.2.2.2.1
  have hyr := cell_range hyc.hr hyc.k7
  have hcw := capWeight_nonneg hv hyr.1 hyr.2
  have hP := capProbability_nonneg c x t
  unfold capTerm
  by_cases hsel : capActive ky c = true
  · rw [if_pos hsel]
    obtain ⟨_, hlev⟩ := capLevel_sound hv hx hx0 hm ht1 ht2 (b := b)
    rw [E3_smul, hy, E1_rvP _ hyc.pr hyc.k7]
    have hcwe := capWeight_cell (List.all_eq_true.mp hyc.cut c hc) hyc.hr
    rw [hcwe] at hcw ⊢
    have := mul_le_mul_of_nonneg_left hlev (mul_nonneg hw hcw)
    push_cast
    nlinarith [this]
  · rw [if_neg hsel, E3_zero]
    have := mul_nonneg (mul_nonneg hw hcw) hP
    linarith

theorem capsLow_le {kr ks : ℕ} {b : Box} {r s t : ℝ} (h : NodeHyp kr ks b r s t) :
    E3 (capsLow kr ks b) (r - 1) (s - 1) t ≤ capsCorrection r s t := by
  unfold capsLow capsCorrection
  rw [E3_psum, List.map_map]
  apply list_sum_map_mono
  intro c hc
  have h0 := capTerm_core (ky := ks) hc false (xsel_false r s t) (xsel_true r s t)
    ⟨h.cp.hs, h.cp.ps, h.cp.ks7, h.cp.oks, h.cs⟩ (by linarith [h.range_r.1]) h.mem h.t1 h.t2
  have h1 := capTerm_core (ky := kr) hc true (xsel_true r s t) (xsel_false r s t)
    ⟨h.cp.hr, h.cp.pr, h.cp.kr7, h.cp.okr, h.cr⟩ (by linarith [h.range_s.1]) h.mem h.t1 h.t2
  simp only [Function.comp, E3_add]
  linarith

/-! ## Tents -/

def tentP (d : ℚ) (sd : Bool) : P3 :=
  A3.add (const3 (1 - 2 * d ^ 2)) (A3.add (A3.smul (-2) (liftX sd [1, 2, 1]))
    (A3.smul (-4 * d) (A3.mul (liftX sd [1, 1]) (liftT [0, 1]))))

theorem E3_tentP {d : ℚ} {sd : Bool} {r s t x : ℝ} (hx : XSel sd r s t x) :
    E3 (tentP d sd) (r - 1) (s - 1) t = 1 - 2 * (x * x + (d : ℝ) * d + 2 * d * x * t) := by
  unfold XSel at hx
  simp only [tentP, E3_add, E3_smul, E3_mul, E3_const3, hx, E3_liftT, E1_quad, E1_lin, E1_T]
  push_cast; ring

def tentTerm (ky : ℕ) (b : Box) (c : Tent) (sd : Bool) : P3 :=
  if 0 < centre b (tentP c.d sd) then
    A3.smul (c.weight / 2) (A3.mul (liftX (!sd) (rvP c.vector ky)) (tentP c.d sd))
  else A3.zero

def tentsLow (kr ks : ℕ) (b : Box) : P3 :=
  psum A2 (tents.map fun c => A3.add (tentTerm ks b c false) (tentTerm kr b c true))

theorem tentTerm_core {ky : ℕ} {b : Box} {r s t x y : ℝ} {c : Tent} (hc : c ∈ tents)
    (sd : Bool) (hx : XSel sd r s t x) (hy : XSel (!sd) r s t y) (hyc : CellOne ky y) :
    E3 (tentTerm ky b c sd) (r - 1) (s - 1) t ≤
      (c.weight : ℝ) * radialValue c.vector y * tentProfile c.d x t / 2 := by
  obtain ⟨hw0, hvv, _⟩ := tent_data_ok c hc
  have hw : (0 : ℝ) ≤ c.weight := by exact_mod_cast hw0
  have hyr := cell_range hyc.hr hyc.k7
  have hrv := radialValue_nonneg _ hvv hyr.1 hyr.2
  have hT : 0 ≤ tentProfile c.d x t := le_max_left _ _
  unfold tentTerm
  by_cases hsel : 0 < centre b (tentP c.d sd)
  · rw [if_pos hsel, E3_smul, E3_mul, hy, E3_tentP hx, E1_rvP _ hyc.pr hyc.k7]
    have hle : 1 - 2 * (x * x + (c.d : ℝ) * c.d + 2 * c.d * x * t) ≤ tentProfile c.d x t :=
      le_max_right _ _
    have := mul_le_mul_of_nonneg_left hle (mul_nonneg hw hrv)
    push_cast
    nlinarith [this]
  · rw [if_neg hsel, E3_zero]
    have := mul_nonneg (mul_nonneg hw hrv) hT
    linarith

theorem tentsLow_le {kr ks : ℕ} {b : Box} {r s t : ℝ} (h : NodeHyp kr ks b r s t) :
    E3 (tentsLow kr ks b) (r - 1) (s - 1) t ≤ tentsCorrection r s t := by
  unfold tentsLow tentsCorrection
  rw [E3_psum, List.map_map]
  apply list_sum_map_mono
  intro c hc
  have h0 := tentTerm_core (ky := ks) (b := b) hc false (xsel_false r s t) (xsel_true r s t)
    ⟨h.cp.hs, h.cp.ps, h.cp.ks7, h.cp.oks, h.cs⟩
  have h1 := tentTerm_core (ky := kr) (b := b) hc true (xsel_true r s t) (xsel_false r s t)
    ⟨h.cp.hr, h.cp.pr, h.cp.kr7, h.cp.okr, h.cr⟩
  simp only [Function.comp, E3_add]
  linarith

/-! ## Allocations -/

def qP : P3 :=
  A3.add (liftU [1, 2, 1]) (A3.add (liftV [1, 2, 1])
    (A3.smul 2 (A3.mul (A3.mul (liftU [1, 1]) (liftV [1, 1])) (liftT [0, 1]))))

theorem E3_qP (r s t : ℝ) : E3 qP (r - 1) (s - 1) t = r * r + s * s + 2 * r * s * t := by
  simp only [qP, E3_add, E3_smul, E3_mul, E3_liftU, E3_liftV, E3_liftT, E1_quad, E1_lin, E1_T]
  push_cast; ring

def oneMinus2q : P3 := A3.add (const3 1) (A3.smul (-2) qP)

def allocR (kr ks : ℕ) (c : AllocationData) : P3 :=
  A3.add (liftU (rvP c.vector kr)) (liftV (rvP c.vector ks))

def allocTerm (kr ks : ℕ) (b : Box) (c : AllocationData) : P3 :=
  if c.twoLevel then
    if pos b (A3.add (const3 (c.inner ^ 2)) (A3.smul (-1) qP)) then
      A3.smul (c.weight / 2) (allocR kr ks c)
    else if nonneg b (A3.add (const3 (c.outer ^ 2)) (A3.smul (-1) qP)) then
      A3.smul (c.weight / 4) (allocR kr ks c)
    else A3.zero
  else if 0 < centre b oneMinus2q then
    A3.smul (c.weight / 2) (A3.mul (allocR kr ks c) oneMinus2q)
  else A3.zero

def allocsLow (kr ks : ℕ) (b : Box) : P3 :=
  psum A2 (allocations.map fun c => allocTerm kr ks b c)

theorem profile_classical {c : AllocationData} (hc : c.twoLevel = false) {q : ℝ} (hq : 0 ≤ q) :
    1 - 2 * q ≤ allocationProfile c q := by
  unfold allocationProfile
  rw [if_neg (by simp [hc])]
  split_ifs with h1 h2
  · linarith
  · exact le_rfl
  · apply le_min
    · linarith
    · have hs := Real.sq_sqrt hq
      have : 0 ≤ (1 - 2 * Real.sqrt q) ^ 2 := sq_nonneg _
      nlinarith [this, hs]

theorem allocTerm_le {kr ks : ℕ} {b : Box} {r s t : ℝ} (h : NodeHyp kr ks b r s t)
    {c : AllocationData} (hc : c ∈ allocations) :
    E3 (allocTerm kr ks b c) (r - 1) (s - 1) t ≤
      (c.weight : ℝ) * (radialValue c.vector r + radialValue c.vector s) *
        allocationProfile c (r * r + s * s + 2 * r * s * t) / 2 := by
  obtain ⟨hw0, hvv, _⟩ := allocation_data_ok c hc
  have hw : (0 : ℝ) ≤ c.weight := by exact_mod_cast hw0
  have hry := h.range_r
  have hsy := h.range_s
  have hR : 0 ≤ radialValue c.vector r + radialValue c.vector s :=
    add_nonneg (radialValue_nonneg _ hvv hry.1 hry.2) (radialValue_nonneg _ hvv hsy.1 hsy.2)
  have hprof := allocationProfile_nonneg c (r * r + s * s + 2 * r * s * t)
  have hRe : E3 (allocR kr ks c) (r - 1) (s - 1) t = radialValue c.vector r + radialValue c.vector s := by
    simp only [allocR, E3_add, E3_liftU, E3_liftV, E1_rvP _ h.cp.pr h.cp.kr7, E1_rvP _ h.cp.ps h.cp.ks7]
  have hq0 : 0 ≤ r * r + s * s + 2 * r * s * t := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r) (by linarith : (0 : ℝ) ≤ s),
      sq_nonneg (r - s), h.t1]
  have hbase : 0 ≤ (c.weight : ℝ) * (radialValue c.vector r + radialValue c.vector s) *
      allocationProfile c (r * r + s * s + 2 * r * s * t) / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hw hR) hprof) (by norm_num)
  unfold allocTerm
  by_cases h2 : c.twoLevel = true
  · rw [if_pos h2]
    by_cases hin : pos b (A3.add (const3 (c.inner ^ 2)) (A3.smul (-1) qP)) = true
    · rw [if_pos hin, E3_smul, hRe]
      have hlt := pos_sound hin h.mem
      rw [E3_add, E3_const3, E3_smul, E3_qP] at hlt
      have hp1 : allocationProfile c (r * r + s * s + 2 * r * s * t) = 1 := by
        unfold allocationProfile
        rw [if_pos h2, if_pos (by push_cast at hlt; linarith)]
      rw [hp1]; push_cast; apply le_of_eq; ring
    · rw [if_neg hin]
      by_cases hout : nonneg b (A3.add (const3 (c.outer ^ 2)) (A3.smul (-1) qP)) = true
      · rw [if_pos hout, E3_smul, hRe]
        have hle := nonneg_sound hout h.mem
        rw [E3_add, E3_const3, E3_smul, E3_qP] at hle
        have hp : 1 / 2 ≤ allocationProfile c (r * r + s * s + 2 * r * s * t) := by
          unfold allocationProfile
          rw [if_pos h2]
          split_ifs
          · norm_num
          · norm_num
          · push_cast at hle; linarith
        have := mul_le_mul_of_nonneg_left hp (mul_nonneg hw hR)
        push_cast
        nlinarith [this]
      · rw [if_neg hout, E3_zero]; exact hbase
  · rw [if_neg h2]
    by_cases hcen : 0 < centre b oneMinus2q
    · rw [if_pos hcen, E3_smul, E3_mul, hRe]
      have hcl := profile_classical (by simpa using h2) hq0
      have he : E3 oneMinus2q (r - 1) (s - 1) t = 1 - 2 * (r * r + s * s + 2 * r * s * t) := by
        simp only [oneMinus2q, E3_add, E3_const3, E3_smul, E3_qP]; push_cast; ring
      rw [he]
      have := mul_le_mul_of_nonneg_left hcl (mul_nonneg hw hR)
      push_cast
      nlinarith [this]
    · rw [if_neg hcen, E3_zero]; exact hbase

theorem allocsLow_le {kr ks : ℕ} {b : Box} {r s t : ℝ} (h : NodeHyp kr ks b r s t) :
    E3 (allocsLow kr ks b) (r - 1) (s - 1) t ≤ allocationsCorrection r s t := by
  unfold allocsLow allocationsCorrection
  rw [E3_psum, List.map_map]
  apply list_sum_map_mono
  intro c hc
  simp only [Function.comp]
  exact allocTerm_le h hc

/-! ## Graphs -/

def inI (lo hi c h : ℚ) : Bool := decide (lo ≤ 1 + c - h) && decide (1 + c + h ≤ hi)
def inI2 (op : Bool) (lo hi c h : ℚ) : Bool :=
  (if op then decide (lo < 1 + c - h) else decide (lo ≤ 1 + c - h)) && decide (1 + c + h ≤ hi)

def graphOK (b : Box) (g : Graph) : Bool :=
  (if g.mixed then
    (inI g.lo1 g.hi1 b.cu b.hu && inI2 g.firstOpen g.lo2 g.hi2 b.cv b.hv) ||
    (inI g.lo1 g.hi1 b.cv b.hv && inI2 g.firstOpen g.lo2 g.hi2 b.cu b.hu)
   else inI g.lo1 g.hi1 b.cu b.hu && inI2 g.firstOpen g.lo2 g.hi2 b.cv b.hv) &&
  decide (g.tlo ≤ b.ct - b.ht) && decide (b.ct + b.ht ≤ g.thi)

def graphLow (b : Box) : ℚ := (graphs.map fun g => if graphOK b g then g.weight else 0).sum

theorem abs_box {x c h : ℝ} (hx : |x - c| ≤ h) : c - h ≤ x ∧ x ≤ c + h := by
  rw [abs_le] at hx; constructor <;> linarith

theorem inI_sound {lo hi c h : ℚ} (hI : inI lo hi c h = true) {x : ℝ}
    (hx : |(x - 1) - c| ≤ h) : (lo : ℝ) ≤ x ∧ x ≤ hi := by
  simp only [inI, Bool.and_eq_true, decide_eq_true_eq] at hI
  have := abs_box hx
  have h1 : ((lo : ℚ) : ℝ) ≤ ((1 + c - h : ℚ) : ℝ) := by exact_mod_cast hI.1
  have h2 : ((1 + c + h : ℚ) : ℝ) ≤ ((hi : ℚ) : ℝ) := by exact_mod_cast hI.2
  push_cast at h1 h2
  constructor <;> linarith

theorem inI2_sound {op : Bool} {lo hi c h : ℚ} (hI : inI2 op lo hi c h = true) {x : ℝ}
    (hx : |(x - 1) - c| ≤ h) :
    (if op then (lo : ℝ) < x else (lo : ℝ) ≤ x) ∧ x ≤ hi := by
  simp only [inI2, Bool.and_eq_true, decide_eq_true_eq] at hI
  have := abs_box hx
  have h2 : ((1 + c + h : ℚ) : ℝ) ≤ ((hi : ℚ) : ℝ) := by exact_mod_cast hI.2
  push_cast at h2
  refine ⟨?_, by linarith⟩
  cases op
  · simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at hI ⊢
    have h1 : ((lo : ℚ) : ℝ) ≤ ((1 + c - h : ℚ) : ℝ) := by exact_mod_cast hI.1
    push_cast at h1; linarith
  · simp only [if_true, decide_eq_true_eq] at hI ⊢
    have h1 : ((lo : ℚ) : ℝ) < ((1 + c - h : ℚ) : ℝ) := by exact_mod_cast hI.1
    push_cast at h1; linarith

theorem graphOK_sound {b : Box} {g : Graph} (hg : graphOK b g = true) {r s t : ℝ}
    (hm : b.Mem (r - 1) (s - 1) t) :
    graphRadial g r s ∧ (g.tlo : ℝ) ≤ t ∧ t ≤ (g.thi : ℝ) := by
  unfold graphOK at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨hrad, htlo⟩, hthi⟩ := hg
  have ht := abs_box hm.2.2
  have h1 : ((g.tlo : ℚ) : ℝ) ≤ ((b.ct - b.ht : ℚ) : ℝ) := by exact_mod_cast htlo
  have h2 : ((b.ct + b.ht : ℚ) : ℝ) ≤ ((g.thi : ℚ) : ℝ) := by exact_mod_cast hthi
  push_cast at h1 h2
  refine ⟨?_, by linarith, by linarith⟩
  unfold graphRadial
  dsimp only
  by_cases hmix : g.mixed = true
  · rw [if_pos hmix] at hrad ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hrad
    rcases hrad with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨inI_sound ha hm.1, inI2_sound hb hm.2.1⟩
    · exact Or.inr ⟨inI_sound ha hm.2.1, inI2_sound hb hm.1⟩
  · rw [if_neg hmix] at hrad ⊢
    simp only [Bool.and_eq_true] at hrad
    exact ⟨inI_sound hrad.1 hm.1, inI2_sound hrad.2 hm.2.1⟩

theorem graphLow_le {b : Box} {r s t : ℝ} (hm : b.Mem (r - 1) (s - 1) t) :
    (graphLow b : ℝ) ≤ graphsCorrection r s t := by
  unfold graphLow graphsCorrection
  rw [cast_sum_map]
  apply list_sum_map_mono
  intro g hg
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (graphOK_sound h1 hm) h2
  · exact_mod_cast graph_weights_nonneg g hg
  · norm_num

/-! ## The node polynomial -/

def nodeP (B : P3) (kr ks : ℕ) (b : Box) : P3 :=
  A3.add B (A3.add (capsLow kr ks b) (A3.add (tentsLow kr ks b)
    (A3.add (allocsLow kr ks b) (const3 (graphLow b)))))

/-- What the base polynomial must satisfy on a cell pair. -/
def BaseOK (B : P3) (lam : ℚ) (kr ks : ℕ) : Prop :=
  ∀ r s t : ℝ, CellPair kr ks r s →
    E3 B (r - 1) (s - 1) t ≤ -corePair r s t +
      (gaugeWeight r * gaugePsi s + gaugeWeight s * gaugePsi r) / 2 -
      lam * (t ^ 4 - (133 / 250) ^ 2 * t ^ 2)

theorem nodeP_le {B : P3} {lam : ℚ} {kr ks : ℕ} (hB : BaseOK B lam kr ks) {b : Box}
    {r s t : ℝ} (h : NodeHyp kr ks b r s t) :
    E3 (nodeP B kr ks b) (r - 1) (s - 1) t ≤ -pair r s t - lam * (t ^ 4 - (133 / 250) ^ 2 * t ^ 2) := by
  have h0 := hB r s t h.cp
  have hc := capsLow_le h
  have ht := tentsLow_le h
  have ha := allocsLow_le h
  have hg := graphLow_le (r := r) (s := s) (t := t) h.mem
  have e : -pair r s t = -corePair r s t + capsCorrection r s t +
      tentsCorrection r s t + allocationsCorrection r s t + graphsCorrection r s t +
      (gaugeWeight r * gaugePsi s + gaugeWeight s * gaugePsi r) / 2 := by
    unfold pair rawPair corePair; ring
  unfold nodeP
  simp only [E3_add, E3_const3]
  rw [e]
  linarith

/-! ## Search -/

def coef (S : P3) (i j k : ℕ) : ℚ := ((S.getD i []).getD j []).getD k 0

/-- Split the coordinate with the largest first plus second order contribution. -/
def chooseAxis (b : Box) (S : P3) : ℕ :=
  let su := |coef S 1 0 0| * b.hu + |coef S 2 0 0| * b.hu ^ 2
  let sv := |coef S 0 1 0| * b.hv + |coef S 0 2 0| * b.hv ^ 2
  let st := |coef S 0 0 1| * b.ht + |coef S 0 0 2| * b.ht ^ 2
  if sv ≤ su ∧ st ≤ su then 0 else if st ≤ sv then 1 else 2

def splitBox (b : Box) : ℕ → Box × Box
  | 0 => (⟨b.cu - b.hu / 2, b.cv, b.ct, b.hu / 2, b.hv, b.ht⟩,
          ⟨b.cu + b.hu / 2, b.cv, b.ct, b.hu / 2, b.hv, b.ht⟩)
  | 1 => (⟨b.cu, b.cv - b.hv / 2, b.ct, b.hu, b.hv / 2, b.ht⟩,
          ⟨b.cu, b.cv + b.hv / 2, b.ct, b.hu, b.hv / 2, b.ht⟩)
  | _ => (⟨b.cu, b.cv, b.ct - b.ht / 2, b.hu, b.hv, b.ht / 2⟩,
          ⟨b.cu, b.cv, b.ct + b.ht / 2, b.hu, b.hv, b.ht / 2⟩)

theorem half_cover {x c h : ℝ} (hx : |x - c| ≤ h) :
    |x - (c - h / 2)| ≤ h / 2 ∨ |x - (c + h / 2)| ≤ h / 2 := by
  rw [abs_le] at hx
  by_cases hc : x ≤ c
  · left; rw [abs_le]; constructor <;> linarith
  · right; rw [abs_le]; constructor <;> linarith

theorem splitBox_cover (b : Box) (ax : ℕ) {u v t : ℝ} (hm : b.Mem u v t) :
    (splitBox b ax).1.Mem u v t ∨ (splitBox b ax).2.Mem u v t := by
  obtain ⟨hu, hv, ht⟩ := hm
  match ax with
  | 0 =>
    rcases half_cover hu with h | h
    · left; refine ⟨?_, hv, ht⟩; simp only [splitBox]; push_cast; exact h
    · right; refine ⟨?_, hv, ht⟩; simp only [splitBox]; push_cast; exact h
  | 1 =>
    rcases half_cover hv with h | h
    · left; refine ⟨hu, ?_, ht⟩; simp only [splitBox]; push_cast; exact h
    · right; refine ⟨hu, ?_, ht⟩; simp only [splitBox]; push_cast; exact h
  | n + 2 =>
    rcases half_cover ht with h | h
    · left; refine ⟨hu, hv, ?_⟩; simp only [splitBox]; push_cast; exact h
    · right; refine ⟨hu, hv, ?_⟩; simp only [splitBox]; push_cast; exact h

def search (B : P3) (kr ks : ℕ) : ℕ → Box → Bool
  | 0, b => decide (0 ≤ lowOn b (nodeP B kr ks b))
  | n + 1, b =>
    let S := shift3 b.cu b.cv b.ct (nodeP B kr ks b)
    if 0 ≤ low3 b.hu b.hv b.ht S then true
    else
      let bs := splitBox b (chooseAxis b S)
      search B kr ks n bs.1 && search B kr ks n bs.2

def Target (lam : ℚ) (r s t : ℝ) : Prop :=
  0 ≤ -pair r s t - lam * (t ^ 4 - (133 / 250) ^ 2 * t ^ 2)

theorem search_sound {B : P3} {lam : ℚ} {kr ks : ℕ} (hB : BaseOK B lam kr ks) :
    ∀ (n : ℕ) (b : Box), search B kr ks n b = true →
      ∀ r s t : ℝ, NodeHyp kr ks b r s t → Target lam r s t
  | 0, b, hs, r, s, t, h => by
    have h0 : (0 : ℝ) ≤ (lowOn b (nodeP B kr ks b) : ℝ) := by
      exact_mod_cast (decide_eq_true_eq.mp hs)
    have := lowOn_sound h.mem (nodeP B kr ks b)
    have := nodeP_le hB h
    unfold Target; linarith
  | n + 1, b, hs, r, s, t, h => by
    simp only [search] at hs
    split_ifs at hs with hlow
    · have h0 : (0 : ℝ) ≤ (lowOn b (nodeP B kr ks b) : ℝ) := by exact_mod_cast hlow
      have := lowOn_sound h.mem (nodeP B kr ks b)
      have := nodeP_le hB h
      unfold Target; linarith
    · simp only [Bool.and_eq_true] at hs
      rcases splitBox_cover b (chooseAxis b (shift3 b.cu b.cv b.ct (nodeP B kr ks b))) h.mem
        with hm | hm
      · exact search_sound hB n _ hs.1 r s t { h with mem := hm }
      · exact search_sound hB n _ hs.2 r s t { h with mem := hm }

/-! ## Cells -/

def rootBox (kr ks : ℕ) : Box :=
  ⟨(cellLo kr + cellHi kr) / 2 - 1, (cellLo ks + cellHi ks) / 2 - 1, (-1 - 133 / 250) / 2,
   (cellHi kr - cellLo kr) / 2, (cellHi ks - cellLo ks) / 2, (1 - 133 / 250) / 2⟩

def checkCell (B : P3) (kr ks fuel : ℕ) : Bool :=
  cellOK kr && cellOK ks && capsCutOK kr && capsCutOK ks && decide (kr < 5) && decide (ks < 5) &&
    search B kr ks fuel (rootBox kr ks)

theorem radialPiece_cell {k : ℕ} {r : ℝ} (hr : InCell k r) (hk : k < 5) : radialPiece r = k := by
  obtain ⟨h1, h2, h3⟩ := hr
  have hr74 : r ≤ 7 / 4 := by
    interval_cases k <;> simp [cellHi, breaks] at h2 <;> linarith
  rw [radialPiece_on_support hr74]
  interval_cases k <;> simp [cellLo, cellHi, breaks] at h1 h2 h3 <;>
    split_ifs <;> first | rfl | (exfalso; linarith)

theorem checkCell_sound {B : P3} {lam : ℚ} {kr ks fuel : ℕ} (hB : BaseOK B lam kr ks)
    (hc : checkCell B kr ks fuel = true) {r s t : ℝ} (hr : InCell kr r) (hs : InCell ks s)
    (ht1 : -1 ≤ t) (ht2 : t ≤ -(133 / 250)) : Target lam r s t := by
  simp only [checkCell, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨okr, oks⟩, cr⟩, cs⟩, kr5⟩, ks5⟩, hsearch⟩ := hc
  have cp : CellPair kr ks r s :=
    ⟨hr, hs, radialPiece_cell hr kr5, radialPiece_cell hs ks5, by omega, by omega, okr, oks⟩
  have hm : (rootBox kr ks).Mem (r - 1) (s - 1) t := by
    obtain ⟨a1, a2, _⟩ := hr
    obtain ⟨b1, b2, _⟩ := hs
    refine ⟨?_, ?_, ?_⟩ <;> simp only [rootBox] <;> push_cast <;> rw [abs_le] <;>
      constructor <;> linarith
  exact search_sound hB fuel _ hsearch r s t ⟨cp, cr, cs, hm, ht1, by linarith⟩

/-- Every radius in `[1, cellHi (j-1)]` lies in a cell below `j`. -/
theorem exists_cell {j : ℕ} (hj : 0 < j) {r : ℝ} (h1 : 1 ≤ r)
    (h2 : r ≤ (cellHi (j - 1) : ℝ)) : ∃ k < j, InCell k r := by
  suffices key : ∀ n k, j - k = n → k < j → (cellLo k : ℝ) ≤ r →
      (0 < k → (cellLo k : ℝ) < r) → ∃ k' < j, InCell k' r by
    exact key (j - 0) 0 rfl hj (by simpa [cellLo, breaks] using h1)
      (fun h => absurd h (lt_irrefl 0))
  intro n
  induction n with
  | zero => intro k hn hk; omega
  | succ n ih =>
    intro k hn hk hlo hstr
    by_cases hle : r ≤ (cellHi k : ℝ)
    · exact ⟨k, hk, hlo, hle, hstr⟩
    · have hk1 : k + 1 < j := by
        by_contra hcon
        have : k = j - 1 := by omega
        rw [this] at hle; exact hle h2
      have hcl : cellLo (k + 1) = cellHi k := rfl
      have hlt : (cellHi k : ℝ) < r := lt_of_not_ge hle
      exact ih (k + 1) (by omega) hk1 (by rw [hcl]; exact hlt.le) (fun _ => by rw [hcl]; exact hlt)

end D4Bound.KBN
