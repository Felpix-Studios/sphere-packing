import D4Bound.CyclicNativeCorr
import D4Bound.CyclicNativePolyEq
import D4Bound.V7PairUpper
import D4Bound.V7PairPolynomial
import D4Bound.V7CyclicUpper

/-!
# Soundness of the native correction lower bounds

Caps are bounded with the radial weight of a fixed piece `p` (`pv`), so the
bounds hold on the whole closed case box; on points owned by region `p` this is
the actual radial weight.
-/
namespace D4Bound.CyclicNative
open D4Bound.V7

noncomputable section

lemma div_le_div_nonpos_num {a b c : ℝ} (ha : a ≤ 0) (hc : 0 < c) (h : c ≤ b) : a / c ≤ a / b := by
  have := div_le_div_of_nonneg_left (neg_nonneg.mpr ha) hc h
  rw [neg_div, neg_div] at this; linarith

/-- Radial value with a fixed piece. -/
def pv (v : List ℚ) (p : ℕ) (r : ℝ) : ℝ :=
  ((List.range 7).map fun i => (v.getD (7*p+i) 0 : ℝ) * basisValue p i r).sum

lemma radialValue_eq_pv (v : List ℚ) (r : ℝ) : radialValue v r = pv v (radialPiece r) r := rfl

lemma radialLo_sound (v : List ℚ) (p : ℕ) {lo hi : ℚ} {r : ℝ}
    (hlo : (lo : ℝ) ≤ r) (hhi : r ≤ (hi : ℝ)) :
    ((radialLo basisIntervals v p lo hi : ℚ) : ℝ) ≤ max 0 (pv v p r) := by
  unfold radialLo
  dsimp only
  split_ifs with h
  · obtain ⟨hw, hz0, hzz, hz1, hv⟩ := h
    apply le_trans _ (le_max_right _ _)
    rw [PairPoly.rat_map_sum]
    unfold pv
    apply list_sum_map_mono
    intro i hi'
    have hi7 : i < 7 := List.mem_range.mp hi'
    have hvi : (0 : ℚ) ≤ v.getD (7*p+i) 0 := by
      have := List.all_eq_true.mp hv i hi'
      simpa using this
    set ab := basisIntervals.getD p (0,1)
    have hwr : (0 : ℝ) < (ab.2 : ℝ) - (ab.1 : ℝ) := by exact_mod_cast hw
    set z : ℝ := (r - ab.1)/((ab.2 : ℝ) - ab.1) with hzdef
    have hzl : ((((lo - ab.1)/(ab.2 - ab.1) : ℚ)) : ℝ) ≤ z := by
      push_cast; exact div_le_div_of_nonneg_right (by linarith) hwr.le
    have hzh : z ≤ ((((hi - ab.1)/(ab.2 - ab.1) : ℚ)) : ℝ) := by
      push_cast; exact div_le_div_of_nonneg_right (by linarith) hwr.le
    have hz0' : (0:ℝ) ≤ (((lo - ab.1)/(ab.2 - ab.1) : ℚ) : ℝ) := by exact_mod_cast hz0
    have hz1' : (((hi - ab.1)/(ab.2 - ab.1) : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hz1
    have hb : basisValue p i r = (Nat.choose 6 i : ℝ) * z^i * (1-z)^(6-i) := by
      simp only [basisValue, hzdef, ab]
    rw [hb, NPoly.choose_eq]
    push_cast
    have h1 : ((((lo:ℝ) - ab.1)/((ab.2:ℝ) - ab.1)))^i ≤ z^i := by
      apply pow_le_pow_left₀ (by push_cast at hz0'; exact hz0') (by push_cast at hzl; exact hzl)
    have h2 : (1 - (((hi:ℝ) - ab.1)/((ab.2:ℝ) - ab.1)))^(6-i) ≤ (1-z)^(6-i) := by
      apply pow_le_pow_left₀ (by push_cast at hz1'; linarith) (by push_cast at hzh; linarith)
    have hvi' : (0:ℝ) ≤ (v.getD (7*p+i) 0 : ℝ) := by exact_mod_cast hvi
    have hc : (0:ℝ) ≤ (Nat.choose 6 i : ℝ) := by positivity
    have hp1 : 0 ≤ ((((lo:ℝ) - ab.1)/((ab.2:ℝ) - ab.1)))^i := by
      apply pow_nonneg; push_cast at hz0'; exact hz0'
    have hp2 : 0 ≤ (1 - (((hi:ℝ) - ab.1)/((ab.2:ℝ) - ab.1)))^(6-i) := by
      apply pow_nonneg; push_cast at hz1'; linarith
    calc (v.getD (7*p+i) 0 : ℝ) * (Nat.choose 6 i : ℝ) * ((((lo:ℝ) - ab.1)/((ab.2:ℝ) - ab.1)))^i *
          (1 - (((hi:ℝ) - ab.1)/((ab.2:ℝ) - ab.1)))^(6-i)
        = (v.getD (7*p+i) 0 : ℝ) * ((Nat.choose 6 i : ℝ) * (((((lo:ℝ) - ab.1)/((ab.2:ℝ) - ab.1)))^i *
          (1 - (((hi:ℝ) - ab.1)/((ab.2:ℝ) - ab.1)))^(6-i))) := by ring
      _ ≤ (v.getD (7*p+i) 0 : ℝ) * ((Nat.choose 6 i : ℝ) * (z^i * (1-z)^(6-i))) := by
          apply mul_le_mul_of_nonneg_left _ hvi'
          apply mul_le_mul_of_nonneg_left _ hc
          exact mul_le_mul h1 h2 hp2 (le_trans hp1 h1)
      _ = (v.getD (7*p+i) 0 : ℝ) * ((Nat.choose 6 i : ℝ) * z^i * (1-z)^(6-i)) := by ring
  · simp

/-- Capped radial weight with a fixed piece. -/
def cwP (c : Cap) (p : ℕ) (r : ℝ) : ℝ :=
  match c.cutoff with
  | none => pv c.vector p r
  | some C => if (C : ℝ) < r then pv c.vector p r else 0

lemma capWeight_eq_cwP (c : Cap) (r : ℝ) : capWeight c r = cwP c (radialPiece r) r := by
  unfold capWeight cwP
  cases c.cutoff <;> rfl

def toCapN (u : Cap → Bool) (c : Cap) : CapN :=
  ⟨c.d, c.a2, c.sigma, c.weight, c.vector, c.cutoff, u c⟩

lemma capWeightLo_sound (u : Cap → Bool) (c : Cap) (p : ℕ) {lo hi : ℚ} {r : ℝ}
    (hlo : (lo : ℝ) ≤ r) (hhi : r ≤ (hi : ℝ)) :
    ((max 0 (capWeightLo basisIntervals (toCapN u c) p lo hi) : ℚ) : ℝ) ≤ max 0 (cwP c p r) := by
  have hr := radialLo_sound c.vector p hlo hhi
  unfold capWeightLo cwP toCapN
  dsimp only
  cases hc : c.cutoff with
  | none =>
    simp only [Rat.cast_max, Rat.cast_zero]
    exact max_le (le_max_left _ _) hr
  | some C =>
    simp only
    split_ifs with h1 h2 h2
    · simp only [Rat.cast_max, Rat.cast_zero]; exact max_le (le_max_left _ _) hr
    · exfalso; apply h2; have : (C : ℝ) < lo := by exact_mod_cast h1
      linarith
    · simp
    · simp

/-! ## Cap probability -/

lemma sqrtUp_ok {q : ℚ} {S : ℝ} (hS : 0 ≤ S) (hSq : S ≤ (q : ℝ)) {dh : ℚ} (hdh : 0 ≤ dh)
    (hq : q ≤ dh^2) : Real.sqrt S ≤ (dh : ℝ) := by
  rw [Real.sqrt_le_left (by exact_mod_cast hdh)]
  have : ((q : ℚ) : ℝ) ≤ ((dh^2 : ℚ) : ℝ) := by exact_mod_cast hq
  push_cast at this
  linarith

lemma sqrtDown_ok {q : ℚ} {S : ℝ} (hSq : (q : ℝ) ≤ S) {dl : ℚ} (hdl : 0 < dl)
    (hq : dl^2 ≤ q) : (dl : ℝ) ≤ Real.sqrt S := by
  apply Real.le_sqrt_of_sq_le
  have : ((dl^2 : ℚ) : ℝ) ≤ ((q : ℚ) : ℝ) := by exact_mod_cast hq
  push_cast at this
  linarith

lemma capProbLo_nonneg (c : CapN) (rlo rhi tlo thi : ℚ) : 0 ≤ capProbLo c rlo rhi tlo thi := by
  unfold capProbLo
  by_cases h0 : 0 < c.d ∧ 0 < rlo ∧ rlo ≤ rhi ∧ tlo ≤ thi ∧ c.sigma^2 ≤ 1
  · rw [if_pos h0]
    by_cases h1 : capAmax c rlo rhi tlo thi ≤ 0
    · rw [if_pos h1]
      by_cases h3 : 0 ≤ sqrtUp (capSmax c tlo thi) ∧ capSmax c tlo thi ≤ sqrtUp (capSmax c tlo thi)^2
      · rw [if_pos h3]
        by_cases h4 : 0 < sqrtUp (capSmax c tlo thi)
        · rw [if_pos h4]
          apply le_min (by norm_num)
          have := div_nonpos_of_nonpos_of_nonneg h1 (le_of_lt h4)
          linarith
        · rw [if_neg h4]; norm_num
      · rw [if_neg h3]
    · rw [if_neg h1]
      by_cases h5 : 0 < sqrtDown (capSmin c tlo thi) ∧ sqrtDown (capSmin c tlo thi)^2 ≤ capSmin c tlo thi
      · rw [if_pos h5]; exact le_max_left _ _
      · rw [if_neg h5]
  · rw [if_neg h0]

/-- Upper bound of `c(r) - sigma t` on a box. -/
lemma capA_le (c : Cap) (u : Cap → Bool) {rlo rhi tlo thi : ℚ} {r t : ℝ} (hd : 0 < c.d)
    (hrl : 0 < rlo) (hr1 : (rlo : ℝ) ≤ r) (hr2 : r ≤ rhi) (ht1 : (tlo : ℝ) ≤ t) (ht2 : t ≤ thi) :
    (r*r + (c.d : ℝ)^2 - (c.a2 : ℝ))/(2*(c.d : ℝ)*r) - (c.sigma : ℝ)*t ≤
      ((capAmax (toCapN u c) rlo rhi tlo thi : ℚ) : ℝ) := by
  have hd' : (0:ℝ) < c.d := by exact_mod_cast hd
  have hrl' : (0:ℝ) < rlo := by exact_mod_cast hrl
  have hr0 : (0:ℝ) < r := by linarith
  have hsplit : (r*r + (c.d : ℝ)^2 - (c.a2 : ℝ))/(2*(c.d : ℝ)*r) =
      r/(2*c.d) + ((c.d:ℝ)^2 - c.a2)/(2*c.d*r) := by field_simp; ring
  rw [hsplit]
  have e1 : r/(2*(c.d:ℝ)) ≤ (rhi:ℝ)/(2*c.d) := div_le_div_of_nonneg_right hr2 (by positivity)
  have e2 : ((c.d:ℝ)^2 - c.a2)/(2*c.d*r) ≤ ((if 0 ≤ c.d^2 - c.a2 then (c.d^2 - c.a2)/(2*c.d*rlo)
        else (c.d^2 - c.a2)/(2*c.d*rhi) : ℚ) : ℝ) := by
    split_ifs with hb
    · have hb' : (0:ℝ) ≤ (c.d:ℝ)^2 - c.a2 := by exact_mod_cast hb
      push_cast
      apply div_le_div_of_nonneg_left hb' (by positivity)
      nlinarith
    · have hb' : (c.d:ℝ)^2 - c.a2 < 0 := by push_neg at hb; exact_mod_cast hb
      push_cast
      exact div_le_div_nonpos_num hb'.le (by positivity) (by nlinarith)
  have e3 : -(c.sigma : ℝ)*t ≤ ((max (-c.sigma*tlo) (-c.sigma*thi) : ℚ) : ℝ) := by
    push_cast
    rcases le_total 0 (c.sigma : ℝ) with hs | hs
    · exact le_trans (by nlinarith) (le_max_left _ _)
    · exact le_trans (by nlinarith) (le_max_right _ _)
  have hdef : ((capAmax (toCapN u c) rlo rhi tlo thi : ℚ) : ℝ) = (rhi:ℝ)/(2*c.d) +
      ((if 0 ≤ c.d^2 - c.a2 then (c.d^2 - c.a2)/(2*c.d*rlo) else (c.d^2 - c.a2)/(2*c.d*rhi) : ℚ) : ℝ) +
      ((max (-c.sigma*tlo) (-c.sigma*thi) : ℚ) : ℝ) := by
    simp only [capAmax, toCapN]; push_cast; ring
  rw [hdef]
  linarith

lemma capSmax_ge (c : Cap) (u : Cap → Bool) {tlo thi : ℚ} {t : ℝ} (ht1 : (tlo : ℝ) ≤ t)
    (ht2 : t ≤ thi) (hk : (0:ℝ) ≤ 1 - (c.sigma:ℝ)^2) :
    (1 - (c.sigma:ℝ)^2)*(1-t*t) ≤ ((capSmax (toCapN u c) tlo thi : ℚ) : ℝ) := by
  simp only [capSmax, toCapN]
  push_cast
  apply mul_le_mul_of_nonneg_left _ hk
  by_cases hz : tlo ≤ 0 ∧ 0 ≤ thi
  · rw [if_pos hz]; push_cast; nlinarith
  · rw [if_neg hz]
    push_neg at hz
    push_cast
    by_cases htl : tlo ≤ 0
    · have hth : (thi:ℝ) < 0 := by exact_mod_cast hz htl
      apply le_trans _ (le_max_right _ _); nlinarith
    · push_neg at htl
      have htl' : (0:ℝ) < tlo := by exact_mod_cast htl
      apply le_trans _ (le_max_left _ _); nlinarith

lemma capSmin_le (c : Cap) (u : Cap → Bool) {tlo thi : ℚ} {t : ℝ} (ht1 : (tlo : ℝ) ≤ t)
    (ht2 : t ≤ thi) (hk : (0:ℝ) ≤ 1 - (c.sigma:ℝ)^2) :
    ((capSmin (toCapN u c) tlo thi : ℚ) : ℝ) ≤ (1 - (c.sigma:ℝ)^2)*(1-t*t) := by
  simp only [capSmin, toCapN]
  push_cast
  apply mul_le_mul_of_nonneg_left _ hk
  rcases le_total 0 t with h | h
  · apply le_trans (min_le_right _ _); nlinarith
  · apply le_trans (min_le_left _ _); nlinarith

lemma capProbLo_sound (c : Cap) (u : Cap → Bool) {rlo rhi tlo thi : ℚ} {r t : ℝ}
    (hr1 : (rlo : ℝ) ≤ r) (hr2 : r ≤ rhi) (ht1 : (tlo : ℝ) ≤ t) (ht2 : t ≤ thi)
    (htm : -1 ≤ t) (htp : t ≤ 1) :
    ((capProbLo (toCapN u c) rlo rhi tlo thi : ℚ) : ℝ) ≤ capProbability c r t := by
  have hP0 := capProbability_nonneg c r t
  unfold capProbLo
  by_cases h0 : 0 < (toCapN u c).d ∧ 0 < rlo ∧ rlo ≤ rhi ∧ tlo ≤ thi ∧ (toCapN u c).sigma^2 ≤ 1
  swap
  · rw [if_neg h0]; simpa using hP0
  rw [if_pos h0]
  obtain ⟨hd, hrl, _, _, hsig⟩ := h0
  have hd' : 0 < c.d := hd
  have hA := capA_le c u hd' hrl hr1 hr2 ht1 ht2
  have hk : (0:ℝ) ≤ 1 - (c.sigma:ℝ)^2 := by
    have : ((c.sigma^2 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hsig
    push_cast at this; linarith
  have hS0 : 0 ≤ (1 - (c.sigma:ℝ)^2)*(1-t*t) := mul_nonneg hk (by nlinarith)
  set S := (1 - (c.sigma:ℝ)^2)*(1-t*t) with hSdef
  set A := (r*r + (c.d : ℝ)^2 - (c.a2 : ℝ))/(2*(c.d : ℝ)*r) - (c.sigma : ℝ)*t with hAdef
  set amax := capAmax (toCapN u c) rlo rhi tlo thi
  have hcp : capProbability c r t = if S = 0 then (if A ≤ 0 then 1 else 0)
      else max 0 (min 1 ((1 - A/Real.sqrt S)/2)) := rfl
  rw [hcp]
  rw [hcp] at hP0
  by_cases h1 : amax ≤ 0
  · rw [if_pos h1]
    have ham : (amax : ℝ) ≤ 0 := by exact_mod_cast h1
    have hAle : A ≤ 0 := by linarith
    by_cases h3 : 0 ≤ sqrtUp (capSmax (toCapN u c) tlo thi) ∧
        capSmax (toCapN u c) tlo thi ≤ sqrtUp (capSmax (toCapN u c) tlo thi)^2
    · rw [if_pos h3]
      have hsq := sqrtUp_ok hS0 (capSmax_ge c u ht1 ht2 hk) h3.1 h3.2
      by_cases h4 : 0 < sqrtUp (capSmax (toCapN u c) tlo thi)
      · rw [if_pos h4]
        by_cases hS : S = 0
        · rw [if_pos hS, if_pos hAle]; push_cast; exact min_le_left _ _
        · rw [if_neg hS]
          have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
          have hsqpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSpos
          apply le_trans _ (le_max_right _ _)
          push_cast
          apply min_le_min_left
          have k1 : A / Real.sqrt S ≤ (amax:ℝ) / Real.sqrt S :=
            div_le_div_of_nonneg_right hA hsqpos.le
          have k2 : (amax:ℝ) / Real.sqrt S ≤ (amax:ℝ) / ((sqrtUp (capSmax (toCapN u c) tlo thi) : ℚ) : ℝ) :=
            div_le_div_nonpos_num ham hsqpos hsq
          linarith
      · rw [if_neg h4]
        have hdh0 : ((sqrtUp (capSmax (toCapN u c) tlo thi) : ℚ) : ℝ) ≤ 0 := by
          push_neg at h4; exact_mod_cast h4
        have hSz : S = 0 := by
          have := Real.sqrt_nonneg S
          have h0' : Real.sqrt S = 0 := by linarith
          rwa [Real.sqrt_eq_zero hS0] at h0'
        rw [if_pos hSz, if_pos hAle]; simp
    · rw [if_neg h3]; simpa using hP0
  · rw [if_neg h1]
    have ham : (0:ℝ) < amax := by push_neg at h1; exact_mod_cast h1
    by_cases h5 : 0 < sqrtDown (capSmin (toCapN u c) tlo thi) ∧
        sqrtDown (capSmin (toCapN u c) tlo thi)^2 ≤ capSmin (toCapN u c) tlo thi
    · rw [if_pos h5]
      have hsq := sqrtDown_ok (capSmin_le c u ht1 ht2 hk) h5.1 h5.2
      have hdl : (0:ℝ) < (sqrtDown (capSmin (toCapN u c) tlo thi) : ℚ) := by exact_mod_cast h5.1
      have hsqpos : 0 < Real.sqrt S := lt_of_lt_of_le hdl hsq
      have hSpos : S ≠ 0 := by
        intro h; rw [h, Real.sqrt_zero] at hsqpos; exact lt_irrefl _ hsqpos
      rw [if_neg hSpos]
      push_cast
      apply max_le_max (le_refl _)
      have k1 : A / Real.sqrt S ≤ (amax:ℝ) / Real.sqrt S :=
        div_le_div_of_nonneg_right hA hsqpos.le
      have k2 : (amax:ℝ) / Real.sqrt S ≤ (amax:ℝ) / ((sqrtDown (capSmin (toCapN u c) tlo thi) : ℚ) : ℝ) :=
        div_le_div_of_nonneg_left ham.le hdl hsq
      have k3 : (1 - (amax:ℝ) / ((sqrtDown (capSmin (toCapN u c) tlo thi) : ℚ) : ℝ))/2 ≤ 1 := by
        have : 0 ≤ (amax:ℝ) / ((sqrtDown (capSmin (toCapN u c) tlo thi) : ℚ) : ℝ) := div_nonneg ham.le hdl.le
        linarith
      apply le_min k3
      linarith
    · rw [if_neg h5]; simpa using hP0

/-! ## One cap and all caps -/

/-- Cap correction with fixed pieces `p` (for `r`) and `q` (for `s`). -/
def capsCorrP (p q : ℕ) (r s t : ℝ) : ℝ :=
  (caps.map fun c => (c.weight : ℝ) *
    (max 0 (cwP c q s) * capProbability c r t + max 0 (cwP c p r) * capProbability c s t)/2).sum

lemma capsCorrP_eq {r s : ℝ} (hr1 : 1 ≤ r) (hr : r ≤ 7/4) (hs1 : 1 ≤ s) (hs : s ≤ 7/4) (t : ℝ) :
    capsCorrP (radialPiece r) (radialPiece s) r s t = capsCorrection r s t := by
  unfold capsCorrP capsCorrection
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  have hv := caps_data_valid c hc
  rw [← capWeight_eq_cwP, ← capWeight_eq_cwP, max_eq_right (capWeight_nonneg hv hs1 hs),
    max_eq_right (capWeight_nonneg hv hr1 hr)]

def cdata (u : Cap → Bool) : CData := ⟨basisIntervals, caps.map (toCapN u)⟩

lemma capsLo_sound (u : Cap → Bool) (p q : ℕ) {rl rh sl sh tl th : ℚ} {r s t : ℝ}
    (hr1 : (rl : ℝ) ≤ r) (hr2 : r ≤ rh) (hs1 : (sl : ℝ) ≤ s) (hs2 : s ≤ sh)
    (ht1 : (tl : ℝ) ≤ t) (ht2 : t ≤ th) (htm : -1 ≤ t) (htp : t ≤ 1) :
    ((capsLo (cdata u) p q rl rh sl sh tl th : ℚ) : ℝ) ≤ capsCorrP p q r s t := by
  unfold capsLo capsCorrP cdata
  dsimp only
  rw [List.map_map, PairPoly.rat_map_sum]
  apply list_sum_map_mono
  intro c hc
  have hv := caps_data_valid c hc
  have hw : (0:ℝ) ≤ c.weight := by exact_mod_cast hv.2.2.2.2.1
  simp only [Function.comp_apply]
  unfold capTermLo
  split_ifs with h
  · have a1 := capWeightLo_sound u c q hs1 hs2
    have a2 := capWeightLo_sound u c p hr1 hr2
    have b1 := capProbLo_sound c u hr1 hr2 ht1 ht2 htm htp
    have b2 := capProbLo_sound c u hs1 hs2 ht1 ht2 htm htp
    have n1 := capProbLo_nonneg (toCapN u c) rl rh tl th
    have n2 := capProbLo_nonneg (toCapN u c) sl sh tl th
    have m1 : (0:ℝ) ≤ ((max 0 (capWeightLo basisIntervals (toCapN u c) q sl sh) : ℚ) : ℝ) := by
      push_cast; exact le_max_left _ _
    have m2 : (0:ℝ) ≤ ((max 0 (capWeightLo basisIntervals (toCapN u c) p rl rh) : ℚ) : ℝ) := by
      push_cast; exact le_max_left _ _
    have n1' : (0:ℝ) ≤ ((capProbLo (toCapN u c) rl rh tl th : ℚ) : ℝ) := by exact_mod_cast n1
    have n2' : (0:ℝ) ≤ ((capProbLo (toCapN u c) sl sh tl th : ℚ) : ℝ) := by exact_mod_cast n2
    have hwc : (toCapN u c).weight = c.weight := rfl
    rw [hwc]
    push_cast at a1 a2 m1 m2 ⊢
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ hw
    exact add_le_add (mul_le_mul a1 b1 n1' (le_trans m1 a1)) (mul_le_mul a2 b2 n2' (le_trans m2 a2))
  · simp only [Rat.cast_zero]
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg hw
    exact add_nonneg (mul_nonneg (le_max_left _ _) (capProbability_nonneg c r t))
      (mul_nonneg (le_max_left _ _) (capProbability_nonneg c s t))

/-! ## Interval quotients and side cosines -/

lemma quotLo_le {n1 d1 d2 : ℚ} {n d : ℝ} (hn : (n1 : ℝ) ≤ n) (hd1 : (d1 : ℝ) ≤ d) (hd2 : d ≤ d2)
    (hpos : 0 < d1) : ((quotLo n1 d1 d2 : ℚ) : ℝ) ≤ n / d := by
  have hp : (0:ℝ) < d1 := by exact_mod_cast hpos
  have hd : 0 < d := by linarith
  unfold quotLo
  split_ifs with h
  · have h' : (0:ℝ) ≤ n1 := by exact_mod_cast h
    push_cast
    calc (n1:ℝ)/d2 ≤ n1/d := div_le_div_of_nonneg_left h' hd hd2
      _ ≤ n/d := div_le_div_of_nonneg_right hn hd.le
  · have h' : (n1:ℝ) < 0 := by push_neg at h; exact_mod_cast h
    push_cast
    calc (n1:ℝ)/d1 ≤ n1/d := div_le_div_nonpos_num h'.le hp hd1
      _ ≤ n/d := div_le_div_of_nonneg_right hn hd.le

lemma le_quotHi {n2 d1 d2 : ℚ} {n d : ℝ} (hn : n ≤ (n2 : ℝ)) (hd1 : (d1 : ℝ) ≤ d) (hd2 : d ≤ d2)
    (hpos : 0 < d1) : n / d ≤ ((quotHi n2 d1 d2 : ℚ) : ℝ) := by
  have hp : (0:ℝ) < d1 := by exact_mod_cast hpos
  have hd : 0 < d := by linarith
  unfold quotHi
  split_ifs with h
  · have h' : (0:ℝ) ≤ n2 := by exact_mod_cast h
    push_cast
    calc n/d ≤ n2/d := div_le_div_of_nonneg_right hn hd.le
      _ ≤ n2/d1 := div_le_div_of_nonneg_left h' hp hd1
  · have h' : (n2:ℝ) < 0 := by push_neg at h; exact_mod_cast h
    push_cast
    calc n/d ≤ n2/d := div_le_div_of_nonneg_right hn hd.le
      _ ≤ n2/d2 := div_le_div_nonpos_num h'.le hd hd2

lemma cos_bounds {rl rh sl sh dl dh : ℚ} {r s d : ℝ} (hrl : 0 < rl) (hsl : 0 < sl) (hdl : 0 ≤ dl)
    (hr1 : (rl:ℝ) ≤ r) (hr2 : r ≤ rh) (hs1 : (sl:ℝ) ≤ s) (hs2 : s ≤ sh)
    (hd1 : (dl:ℝ) ≤ d) (hd2 : d ≤ dh) :
    ((cosLo rl rh sl sh dl dh : ℚ) : ℝ) ≤ sideCos r s d ∧
      sideCos r s d ≤ ((cosHi rl rh sl sh dl dh : ℚ) : ℝ) := by
  have hrl' : (0:ℝ) < rl := by exact_mod_cast hrl
  have hsl' : (0:ℝ) < sl := by exact_mod_cast hsl
  have hdl' : (0:ℝ) ≤ dl := by exact_mod_cast hdl
  have hpos : (0:ℚ) < 2*rl*sl := by positivity
  have hden1 : ((2*rl*sl : ℚ) : ℝ) ≤ 2*r*s := by push_cast; nlinarith
  have hden2 : 2*r*s ≤ ((2*rh*sh : ℚ) : ℝ) := by push_cast; nlinarith
  unfold sideCos cosLo cosHi
  constructor
  · apply quotLo_le _ hden1 hden2 hpos
    push_cast; nlinarith
  · apply le_quotHi _ hden1 hden2 hpos
    push_cast; nlinarith

lemma sideCos_abs {r s d : ℝ} (hr1 : 1 ≤ r) (hr : r ≤ 7/4) (hs1 : 1 ≤ s) (hs : s ≤ 7/4)
    (hd1 : 1 ≤ d) (hd : d ≤ 7/4) : -1 ≤ sideCos r s d ∧ sideCos r s d ≤ 1 := by
  unfold sideCos
  have hp : 0 < 2*r*s := by positivity
  constructor
  · rw [le_div_iff₀ hp]; nlinarith
  · rw [div_le_iff₀ hp]; nlinarith

end
end D4Bound.CyclicNative

#print axioms D4Bound.CyclicNative.capsLo_sound
#print axioms D4Bound.CyclicNative.cos_bounds
