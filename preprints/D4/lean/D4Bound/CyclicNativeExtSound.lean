import D4Bound.CyclicNativeCorrSound

/-!
# Soundness of the native exterior correction bounds

Tents, graphs and allocations, with radial weights of fixed pieces, plus the
exterior side-cosine enclosure `t = -1 + z h(r,s)`.
-/
namespace D4Bound.CyclicNative
open D4Bound.V7

noncomputable section

lemma prod_bounds {rl rh tl th : ℚ} {r t : ℝ} (hrl : (0:ℝ) ≤ rl) (hr1 : (rl:ℝ) ≤ r) (hr2 : r ≤ rh)
    (ht1 : (tl:ℝ) ≤ t) (ht2 : t ≤ th) :
    ((prodLo rl rh tl th : ℚ) : ℝ) ≤ r*t ∧ r*t ≤ ((prodHi rl rh tl th : ℚ) : ℝ) := by
  unfold prodLo prodHi
  push_cast
  constructor
  · rcases le_total 0 t with h | h
    · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (by nlinarith)
    · exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (by nlinarith)
  · rcases le_total 0 t with h | h
    · exact le_trans (by nlinarith) (le_trans (le_max_right _ _) (le_max_right _ _))
    · exact le_trans (by nlinarith) (le_trans (le_max_right _ _) (le_max_left _ _))

lemma tentProfLo_sound {d rl rh tl th : ℚ} {r t : ℝ} (hrl : (0:ℝ) ≤ rl) (hr1 : (rl:ℝ) ≤ r)
    (hr2 : r ≤ rh) (ht1 : (tl:ℝ) ≤ t) (ht2 : t ≤ th) :
    ((tentProfLo d rl rh tl th : ℚ) : ℝ) ≤ tentProfile d r t := by
  obtain ⟨p1, p2⟩ := prod_bounds hrl hr1 hr2 ht1 ht2
  unfold tentProfLo tentProfile
  push_cast
  apply max_le_max (le_refl _)
  have hr2' : r^2 ≤ (rh:ℝ)^2 := by nlinarith
  split_ifs with hd
  · have hd' : (0:ℝ) ≤ d := by exact_mod_cast hd
    have := mul_le_mul_of_nonneg_left p2 (by linarith : (0:ℝ) ≤ 2*d)
    push_cast
    nlinarith
  · have hd' : (d:ℝ) < 0 := by push_neg at hd; exact_mod_cast hd
    have := mul_le_mul_of_nonpos_left p1 (by linarith : (2*d:ℝ) ≤ 0)
    push_cast
    nlinarith

def toTentN (c : Tent) : TentN := ⟨c.d, c.weight, c.vector⟩

def tentsCorrP (p q : ℕ) (r s t : ℝ) : ℝ :=
  (tents.map fun c => (c.weight : ℝ) *
    (max 0 (pv c.vector q s) * tentProfile c.d r t + max 0 (pv c.vector p r) * tentProfile c.d s t)/2).sum

lemma tentsCorrP_eq {r s : ℝ} (hr1 : 1 ≤ r) (hr : r ≤ 7/4) (hs1 : 1 ≤ s) (hs : s ≤ 7/4) (t : ℝ) :
    tentsCorrP (radialPiece r) (radialPiece s) r s t = tentsCorrection r s t := by
  unfold tentsCorrP tentsCorrection
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  obtain ⟨_, hv, _⟩ := tent_data_ok c hc
  rw [← radialValue_eq_pv, ← radialValue_eq_pv, max_eq_right (radialValue_nonneg _ hv hs1 hs),
    max_eq_right (radialValue_nonneg _ hv hr1 hr)]

lemma tentsCorrP_nonneg (p q : ℕ) (r s t : ℝ) : 0 ≤ tentsCorrP p q r s t := by
  unfold tentsCorrP
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hw, _, _⟩ := tent_data_ok c hc
  apply div_nonneg _ (by norm_num)
  apply mul_nonneg (Rat.cast_nonneg.mpr hw)
  exact add_nonneg (mul_nonneg (le_max_left _ _) (le_max_left _ _))
    (mul_nonneg (le_max_left _ _) (le_max_left _ _))

lemma tentsLo_sound (p q : ℕ) {rl rh sl sh tl th : ℚ} {r s t : ℝ} (hrl : (0:ℝ) ≤ rl) (hsl : (0:ℝ) ≤ sl)
    (hr1 : (rl : ℝ) ≤ r) (hr2 : r ≤ rh) (hs1 : (sl : ℝ) ≤ s) (hs2 : s ≤ sh)
    (ht1 : (tl : ℝ) ≤ t) (ht2 : t ≤ th) :
    ((((tents.map toTentN).map fun c => tentTermLo basisIntervals c p q rl rh sl sh tl th).sum : ℚ) : ℝ)
      ≤ tentsCorrP p q r s t := by
  unfold tentsCorrP
  rw [List.map_map, PairPoly.rat_map_sum]
  apply list_sum_map_mono
  intro c hc
  obtain ⟨hw0, _, _⟩ := tent_data_ok c hc
  have hw : (0:ℝ) ≤ c.weight := by exact_mod_cast hw0
  simp only [Function.comp_apply]
  unfold tentTermLo toTentN
  dsimp only
  rw [if_pos hw0]
  have a1 := radialLo_sound c.vector q hs1 hs2
  have a2 := radialLo_sound c.vector p hr1 hr2
  have b1 := tentProfLo_sound (d := c.d) hrl hr1 hr2 ht1 ht2
  have b2 := tentProfLo_sound (d := c.d) hsl hs1 hs2 ht1 ht2
  have n1 : (0:ℝ) ≤ ((tentProfLo c.d rl rh tl th : ℚ) : ℝ) := by
    unfold tentProfLo; push_cast; exact le_max_left _ _
  have n2 : (0:ℝ) ≤ ((tentProfLo c.d sl sh tl th : ℚ) : ℝ) := by
    unfold tentProfLo; push_cast; exact le_max_left _ _
  have a1' : ((max 0 (radialLo basisIntervals c.vector q sl sh) : ℚ) : ℝ) ≤ max 0 (pv c.vector q s) := by
    push_cast; exact max_le (le_max_left _ _) a1
  have a2' : ((max 0 (radialLo basisIntervals c.vector p rl rh) : ℚ) : ℝ) ≤ max 0 (pv c.vector p r) := by
    push_cast; exact max_le (le_max_left _ _) a2
  have m1 : (0:ℝ) ≤ ((max 0 (radialLo basisIntervals c.vector q sl sh) : ℚ) : ℝ) := by
    push_cast; exact le_max_left _ _
  have m2 : (0:ℝ) ≤ ((max 0 (radialLo basisIntervals c.vector p rl rh) : ℚ) : ℝ) := by
    push_cast; exact le_max_left _ _
  push_cast at a1' a2' m1 m2 ⊢
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_left _ hw
  exact add_le_add (mul_le_mul a1' b1 n1 (le_trans m1 a1')) (mul_le_mul a2' b2 n2 (le_trans m2 a2'))

/-! ## Graphs -/

def toGraphN (g : Graph) : GraphN :=
  ⟨g.weight, g.lo1, g.hi1, g.lo2, g.hi2, g.tlo, g.thi, g.firstOpen, g.mixed⟩

lemma graphsLo_sound {rl rh sl sh tl th : ℚ} {r s t : ℝ}
    (hr1 : (rl : ℝ) ≤ r) (hr2 : r ≤ rh) (hs1 : (sl : ℝ) ≤ s) (hs2 : s ≤ sh)
    (ht1 : (tl : ℝ) ≤ t) (ht2 : t ≤ th) :
    ((((graphs.map toGraphN).map fun g => graphTermLo g rl rh sl sh tl th).sum : ℚ) : ℝ)
      ≤ graphsCorrection r s t := by
  unfold graphsCorrection
  rw [List.map_map, PairPoly.rat_map_sum]
  apply list_sum_map_mono
  intro g hg
  have hw : (0:ℝ) ≤ g.weight := by exact_mod_cast graph_weights_nonneg g hg
  simp only [Function.comp_apply]
  unfold graphTermLo toGraphN
  dsimp only
  split_ifs with h1 h2
  · rfl
  · exfalso; apply h2
    obtain ⟨_, htl, hth, hc⟩ := h1
    have htl0 : ((g.tlo:ℚ):ℝ) ≤ tl := by exact_mod_cast htl
    have hth0 : (th:ℝ) ≤ ((g.thi:ℚ):ℝ) := by exact_mod_cast hth
    have htl' : (g.tlo : ℝ) ≤ t := by linarith
    have hth' : t ≤ (g.thi : ℝ) := by linarith
    refine ⟨?_, htl', hth'⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, inFirst, inSecond, decide_eq_true_eq] at hc
    have first_of : ∀ (a b : ℚ) (x : ℝ), (a:ℝ) ≤ x → x ≤ b → g.lo1 ≤ a ∧ b ≤ g.hi1 →
        (g.lo1 : ℝ) ≤ x ∧ x ≤ (g.hi1 : ℝ) := by
      intro a b x h1 h2 ⟨k1, k2⟩
      have : (g.lo1:ℝ) ≤ a := by exact_mod_cast k1
      have : (b:ℝ) ≤ g.hi1 := by exact_mod_cast k2
      constructor <;> linarith
    have second_of : ∀ (a b : ℚ) (x : ℝ), (a:ℝ) ≤ x → x ≤ b →
        ((if g.firstOpen then decide (g.lo2 < a) else decide (g.lo2 ≤ a)) = true ∧ b ≤ g.hi2) →
        ((if g.firstOpen then (g.lo2 : ℝ) < x else (g.lo2 : ℝ) ≤ x) ∧ x ≤ (g.hi2 : ℝ)) := by
      intro a b x h1 h2 ⟨k1, k2⟩
      have : (b:ℝ) ≤ g.hi2 := by exact_mod_cast k2
      refine ⟨?_, by linarith⟩
      split_ifs at k1 ⊢ with hf
      · have : (g.lo2:ℝ) < a := by exact_mod_cast (of_decide_eq_true k1)
        linarith
      · have : (g.lo2:ℝ) ≤ a := by exact_mod_cast (of_decide_eq_true k1)
        linarith
    unfold graphRadial
    dsimp only
    rcases hc with ⟨c1, c2⟩ | ⟨⟨hm, c1⟩, c2⟩
    · have A := first_of _ _ _ hr1 hr2 c1
      have Bq := second_of _ _ _ hs1 hs2 c2
      by_cases hm : g.mixed = true
      · rw [if_pos hm]; exact Or.inl ⟨A, Bq⟩
      · rw [if_neg hm]; exact ⟨A, Bq⟩
    · have A := first_of _ _ _ hs1 hs2 c1
      have Bq := second_of _ _ _ hr1 hr2 c2
      rw [if_pos hm]
      exact Or.inr ⟨A, Bq⟩
  all_goals (first | (simp only [Rat.cast_zero]; exact hw) | simp)

/-! ## Allocations -/

def toAllocN (c : AllocationData) : AllocN := ⟨c.weight, c.vector, c.twoLevel, c.inner, c.outer⟩

lemma allocProfLo_sound (c : AllocationData) {qh : ℚ} {x : ℝ} (hx : x ≤ qh) :
    ((allocProfLo (toAllocN c) qh : ℚ) : ℝ) ≤ allocationProfile c x := by
  have h0 := allocationProfile_nonneg c x
  have half : x < 1/4 → (1/2:ℝ) ≤ min 1 (2*(1-Real.sqrt x)^2) := by
    intro hx4
    have hs : Real.sqrt x < 1/2 := by
      rcases le_or_gt x 0 with hneg | hpos
      · rw [Real.sqrt_eq_zero'.mpr hneg]; norm_num
      · rw [show (1/2:ℝ) = Real.sqrt (1/4) by
          rw [show (1/4:ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt hpos.le hx4
    apply le_min (by norm_num)
    nlinarith [Real.sqrt_nonneg x]
  have cq : ∀ a : ℚ, ((a:ℚ):ℝ) = (a:ℝ) := fun a => rfl
  unfold allocProfLo toAllocN
  dsimp only
  by_cases ht : c.twoLevel
  · simp only [ht, if_true]
    by_cases h1 : qh < c.inner^2
    · rw [if_pos h1]
      have h1' : ((qh:ℚ):ℝ) < ((c.inner^2 : ℚ) : ℝ) := by exact_mod_cast h1
      push_cast at h1'
      unfold allocationProfile; rw [if_pos ht, if_pos (by linarith)]; norm_num
    · rw [if_neg h1]
      by_cases h2 : qh ≤ c.outer^2
      · rw [if_pos h2]
        have h2' : ((qh:ℚ):ℝ) ≤ ((c.outer^2 : ℚ) : ℝ) := by exact_mod_cast h2
        push_cast at h2'
        unfold allocationProfile; rw [if_pos ht]
        split_ifs <;> norm_num
        linarith
      · rw [if_neg h2]; simpa using h0
  · simp only [ht, Bool.false_eq_true, if_false]
    by_cases h1 : 1/2 ≤ qh
    · rw [if_pos h1]; simpa using h0
    · rw [if_neg h1]
      have h1q : qh < 1/2 := lt_of_not_ge h1
      have hq2 : (qh:ℝ) < 1/2 := by
        have := (Rat.cast_lt (K := ℝ)).mpr h1q; push_cast at this; exact this
      have hft : c.twoLevel = false := by simpa using ht
      by_cases h2 : 1/4 ≤ qh
      · rw [if_pos h2]
        have hq4 : (1/4:ℝ) ≤ qh := by
          have := (Rat.cast_le (K := ℝ)).mpr h2; push_cast at this; exact this
        unfold allocationProfile
        rw [hft]; simp only [Bool.false_eq_true, if_false]
        rw [if_neg (by linarith)]
        split_ifs with h3
        · push_cast; linarith
        · have := half (lt_of_not_ge h3)
          push_cast; linarith
      · rw [if_neg h2]
        have hq4 : (qh:ℝ) < 1/4 := by
          have := (Rat.cast_lt (K := ℝ)).mpr (lt_of_not_ge h2); push_cast at this; exact this
        unfold allocationProfile
        rw [hft]; simp only [Bool.false_eq_true, if_false]
        rw [if_neg (by linarith), if_neg (by linarith)]
        have := half (by linarith)
        push_cast; linarith

def allocsCorrP (p q : ℕ) (r s t : ℝ) : ℝ :=
  (allocations.map fun c => (c.weight : ℝ) *
    (max 0 (pv c.vector p r) + max 0 (pv c.vector q s)) * allocationProfile c (r*r+s*s+2*r*s*t)/2).sum

lemma allocsCorrP_eq {r s : ℝ} (hr1 : 1 ≤ r) (hr : r ≤ 7/4) (hs1 : 1 ≤ s) (hs : s ≤ 7/4) (t : ℝ) :
    allocsCorrP (radialPiece r) (radialPiece s) r s t = allocationsCorrection r s t := by
  unfold allocsCorrP allocationsCorrection
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  obtain ⟨_, hv, _⟩ := allocation_data_ok c hc
  rw [← radialValue_eq_pv, ← radialValue_eq_pv, max_eq_right (radialValue_nonneg _ hv hs1 hs),
    max_eq_right (radialValue_nonneg _ hv hr1 hr)]

lemma allocsCorrP_nonneg (p q : ℕ) (r s t : ℝ) : 0 ≤ allocsCorrP p q r s t := by
  unfold allocsCorrP
  apply List.sum_nonneg
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hw, _, _⟩ := allocation_data_ok c hc
  apply div_nonneg _ (by norm_num)
  exact mul_nonneg (mul_nonneg (Rat.cast_nonneg.mpr hw)
    (add_nonneg (le_max_left _ _) (le_max_left _ _))) (allocationProfile_nonneg c _)

lemma allocsLo_sound (p q : ℕ) {rl rh sl sh qh : ℚ} {r s t : ℝ}
    (hr1 : (rl : ℝ) ≤ r) (hr2 : r ≤ rh) (hs1 : (sl : ℝ) ≤ s) (hs2 : s ≤ sh)
    (hq : r*r+s*s+2*r*s*t ≤ qh) :
    ((((allocations.map toAllocN).map fun c => allocTermLo basisIntervals c p q rl rh sl sh qh).sum : ℚ) : ℝ)
      ≤ allocsCorrP p q r s t := by
  unfold allocsCorrP
  rw [List.map_map, PairPoly.rat_map_sum]
  apply list_sum_map_mono
  intro c hc
  obtain ⟨hw0, _, _⟩ := allocation_data_ok c hc
  have hw : (0:ℝ) ≤ c.weight := by exact_mod_cast hw0
  simp only [Function.comp_apply]
  unfold allocTermLo
  rw [if_pos (show (0:ℚ) ≤ (toAllocN c).weight from hw0)]
  have a1 := radialLo_sound c.vector p hr1 hr2
  have a2 := radialLo_sound c.vector q hs1 hs2
  have b := allocProfLo_sound c hq
  have nb : (0:ℝ) ≤ ((allocProfLo (toAllocN c) qh : ℚ) : ℝ) := by
    have : (0:ℚ) ≤ allocProfLo (toAllocN c) qh := by
      unfold allocProfLo
      split_ifs <;> (try push_neg at *) <;> first | linarith | norm_num
    exact_mod_cast this
  have hsum : ((max 0 (radialLo basisIntervals c.vector p rl rh) + max 0 (radialLo basisIntervals c.vector q sl sh) : ℚ) : ℝ)
      ≤ max 0 (pv c.vector p r) + max 0 (pv c.vector q s) := by
    push_cast
    exact add_le_add (max_le (le_max_left _ _) a1) (max_le (le_max_left _ _) a2)
  have hs0 : (0:ℝ) ≤ ((max 0 (radialLo basisIntervals c.vector p rl rh) + max 0 (radialLo basisIntervals c.vector q sl sh) : ℚ) : ℝ) := by
    push_cast; exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  have hwc : (toAllocN c).weight = c.weight := rfl
  have hvc : (toAllocN c).vector = c.vector := rfl
  rw [hwc, hvc]
  push_cast at hsum hs0 ⊢
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hw
  exact mul_le_mul hsum b nb (le_trans hs0 hsum)

/-! ## Exterior side cosine and squared distance -/

def extT (r s z : ℝ) : ℝ := -1 + z*(((r+s)^2-(7/4)^2)/(2*r*s))

lemma extT_bounds {rl rh sl sh zl zh : ℚ} {r s z : ℝ} (hrl : 1 ≤ (rl:ℝ)) (hsl : 1 ≤ (sl:ℝ))
    (hr1 : (rl:ℝ) ≤ r) (hr2 : r ≤ rh) (hs1 : (sl:ℝ) ≤ s) (hs2 : s ≤ sh)
    (hz0 : (0:ℝ) ≤ zl) (hz1 : (zl:ℝ) ≤ z) (hz2 : z ≤ zh) :
    ((extTLo rl rh sl sh zl : ℚ) : ℝ) ≤ extT r s z ∧ extT r s z ≤ ((extTHi rl rh sl sh zh : ℚ) : ℝ) := by
  have hpos : (0:ℚ) < 2*rl*sl := by
    have : (0:ℝ) < 2*rl*sl := by positivity
    exact_mod_cast this
  have hden1 : ((2*rl*sl : ℚ) : ℝ) ≤ 2*r*s := by push_cast; nlinarith
  have hden2 : 2*r*s ≤ ((2*rh*sh : ℚ) : ℝ) := by push_cast; nlinarith
  have hn1 : ((((rl+sl)^2 - 49/16) : ℚ) : ℝ) ≤ (r+s)^2-(7/4)^2 := by push_cast; nlinarith
  have hn2 : (r+s)^2-(7/4)^2 ≤ ((((rh+sh)^2 - 49/16) : ℚ) : ℝ) := by push_cast; nlinarith
  have hlo := quotLo_le hn1 hden1 hden2 hpos
  have hhi := le_quotHi hn2 hden1 hden2 hpos
  have q1 : (1:ℚ) ≤ rl := by exact_mod_cast hrl
  have q2 : (1:ℚ) ≤ sl := by exact_mod_cast hsl
  have q3 : (1:ℚ) ≤ rh := by have : (1:ℝ) ≤ rh := by linarith
                             exact_mod_cast this
  have q4 : (1:ℚ) ≤ sh := by have : (1:ℝ) ≤ sh := by linarith
                             exact_mod_cast this
  have hn10 : (0:ℚ) ≤ (rl+sl)^2 - 49/16 := by nlinarith
  have hq0q : (0:ℚ) ≤ quotLo ((rl+sl)^2 - 49/16) (2*rl*sl) (2*rh*sh) := by
    unfold quotLo; rw [if_pos hn10]
    apply div_nonneg hn10; nlinarith
  have hq0 : (0:ℝ) ≤ ((quotLo ((rl+sl)^2 - 49/16) (2*rl*sl) (2*rh*sh) : ℚ) : ℝ) := by
    exact_mod_cast hq0q
  have hh0 : 0 ≤ ((r+s)^2-(7/4)^2)/(2*r*s) := le_trans hq0 hlo
  unfold extT extTLo extTHi
  push_cast
  constructor
  · have := mul_le_mul hz1 hlo hq0 (by linarith)
    linarith
  · have := mul_le_mul hz2 hhi hh0 (by linarith)
    linarith

lemma sqDist_le {rl rh sl sh zh : ℚ} {r s z : ℝ} (hrl : 1 ≤ (rl:ℝ)) (hsl : 1 ≤ (sl:ℝ))
    (hr1 : (rl:ℝ) ≤ r) (hr2 : r ≤ rh) (hs1 : (sl:ℝ) ≤ s) (hs2 : s ≤ sh)
    (hz0 : (0:ℝ) ≤ z) (hz2 : z ≤ zh) :
    r*r + s*s + 2*r*s*extT r s z ≤ ((sqDistHi rl rh sl sh zh : ℚ) : ℝ) := by
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < s := by linarith
  have key : r*r + s*s + 2*r*s*extT r s z = (r-s)^2 + z*((r+s)^2-(7/4)^2) := by
    unfold extT; field_simp; ring
  rw [key]
  unfold sqDistHi
  push_cast
  have hsq : (r-s)^2 ≤ max (((rl:ℝ)-sh)^2) (((rh:ℝ)-sl)^2) := by
    rcases le_total 0 (r-s) with h | h
    · exact le_trans (by nlinarith) (le_max_right _ _)
    · exact le_trans (by nlinarith) (le_max_left _ _)
  have hb0 : 0 ≤ (r+s)^2-(7/4)^2 := by nlinarith
  have hb1 : (r+s)^2-(7/4)^2 ≤ ((rh:ℝ)+sh)^2 - 49/16 := by nlinarith
  have := mul_le_mul hz2 hb1 hb0 (by linarith)
  linarith

lemma extT_abs {r s z : ℝ} (hr1 : 1 ≤ r) (hr : r ≤ 7/4) (hs1 : 1 ≤ s) (hs : s ≤ 7/4)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : -1 ≤ extT r s z ∧ extT r s z ≤ 1 := by
  have hp : 0 < 2*r*s := by positivity
  have hh0 : 0 ≤ ((r+s)^2-(7/4)^2)/(2*r*s) := div_nonneg (by nlinarith) hp.le
  have hh1 : ((r+s)^2-(7/4)^2)/(2*r*s) ≤ 2 := by rw [div_le_iff₀ hp]; nlinarith
  unfold extT
  constructor
  · nlinarith
  · have : z*(((r+s)^2-(7/4)^2)/(2*r*s)) ≤ ((r+s)^2-(7/4)^2)/(2*r*s) := by nlinarith
    linarith

end
end D4Bound.CyclicNative

#print axioms D4Bound.CyclicNative.graphsLo_sound
#print axioms D4Bound.CyclicNative.allocsLo_sound
#print axioms D4Bound.CyclicNative.tentsLo_sound
#print axioms D4Bound.CyclicNative.extT_bounds
