import D4Bound.SphereMeasureCoordinate

/-! Exact description of a nonnegative conical sector by two circular solids. -/
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace D4Bound.SphereMeasure
noncomputable section
open Classical

def sectorSlice (a : ℝ) : Set (ℝ × R2) :=
  {p | p.1^2 + ‖p.2‖^2 ≤ 1 ∧ 0 ≤ p.1 ∧ a^2*(p.1^2+‖p.2‖^2) ≤ p.1^2}

theorem sectorSlice_measurable (a : ℝ) : MeasurableSet (sectorSlice a) := by
  have h1 : MeasurableSet {p : ℝ × R2 | p.1^2+‖p.2‖^2 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have h2 : MeasurableSet {p : ℝ × R2 | 0 ≤ p.1} :=
    measurableSet_le measurable_const measurable_fst
  have h3 : MeasurableSet {p : ℝ × R2 | a^2*(p.1^2+‖p.2‖^2) ≤ p.1^2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  exact h1.inter (h2.inter h3)

theorem closedSector_eq_split {a : ℝ} (ha : 0 ≤ a) :
    closedSector pole a = split ⁻¹' sectorSlice a := by
  ext x
  change (‖x‖ ≤ 1 ∧ a*‖x‖ ≤ ⟪x,pole⟫) ↔
    ((split x).1^2+‖(split x).2‖^2 ≤ 1 ∧ 0 ≤ (split x).1 ∧
      a^2*((split x).1^2+‖(split x).2‖^2) ≤ (split x).1^2)
  rw [← split_norm_sq,inner_pole]
  change (‖x‖ ≤ 1 ∧ a*‖x‖ ≤ x 0) ↔
    (‖x‖^2 ≤ 1 ∧ 0 ≤ x 0 ∧ a^2*‖x‖^2 ≤ (x 0)^2)
  have hm : 0 ≤ a*‖x‖ := mul_nonneg ha (norm_nonneg _)
  constructor
  · rintro ⟨hn,hz⟩
    refine ⟨by nlinarith [norm_nonneg x], le_trans hm hz, ?_⟩
    have hsq := (sq_le_sq₀ hm (le_trans hm hz)).mpr hz
    simpa only [mul_pow] using hsq
  · rintro ⟨hn,hz,hsq⟩
    refine ⟨by nlinarith [norm_nonneg x], ?_⟩
    apply (sq_le_sq₀ hm hz).mp
    simpa only [mul_pow] using hsq

theorem diskSolid_mem_iff {l u : ℝ} {f : ℝ → ℝ} (p : ℝ × R2)
    (hn : 0 ≤ f p.1) :
    p ∈ diskSolid l u f ↔ p.1 ∈ Icc l u ∧ ‖p.2‖^2 ≤ f p.1 := by
  simp only [diskSolid,mem_setOf_eq,Metric.mem_closedBall,dist_zero_right,
    Real.le_sqrt (norm_nonneg p.2) hn]

theorem sectorSlice_eq_union {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    sectorSlice a = diskSolid 0 a (fun z => (1-a^2)/a^2*z^2) ∪
      diskSolid a 1 (fun z => 1-z^2) := by
  ext p
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hk : 0 ≤ (1-a^2)/a^2*p.1^2 :=
    mul_nonneg (div_nonneg (by nlinarith) ha2.le) (sq_nonneg _)
  have hlower : p ∈ diskSolid 0 a (fun z => (1-a^2)/a^2*z^2) ↔
      0 ≤ p.1 ∧ p.1 ≤ a ∧ a^2*‖p.2‖^2 ≤ (1-a^2)*p.1^2 := by
    rw [diskSolid_mem_iff p hk]
    simp only [Set.mem_Icc,div_mul_eq_mul_div,le_div_iff₀ ha2]
    constructor
    · rintro ⟨⟨h0,h1⟩,h2⟩
      exact ⟨h0,h1,by nlinarith only [h2]⟩
    · rintro ⟨h0,h1,h2⟩
      exact ⟨⟨h0,h1⟩,by nlinarith only [h2]⟩
  have hupper : p ∈ diskSolid a 1 (fun z => 1-z^2) ↔
      a ≤ p.1 ∧ p.1 ≤ 1 ∧ ‖p.2‖^2 ≤ 1-p.1^2 := by
    constructor
    · rintro ⟨hp,hb⟩
      have hn : 0 ≤ 1-p.1^2 := by nlinarith [hp.1,hp.2]
      have h := (diskSolid_mem_iff (f := fun z => 1-z^2) p hn).mp ⟨hp,hb⟩
      exact ⟨hp.1,hp.2,h.2⟩
    · rintro ⟨h0,h1,h2⟩
      exact (diskSolid_mem_iff p (by nlinarith [sq_nonneg ‖p.2‖])).mpr ⟨⟨h0,h1⟩,h2⟩
  rw [Set.mem_union,hlower,hupper]
  change (p.1^2+‖p.2‖^2 ≤ 1 ∧ 0 ≤ p.1 ∧
    a^2*(p.1^2+‖p.2‖^2) ≤ p.1^2) ↔ _
  constructor
  · rintro ⟨hn,hz,hc⟩
    rcases le_total p.1 a with hz1 | hz1
    · exact Or.inl ⟨hz,hz1,by nlinarith only [hc]⟩
    · exact Or.inr ⟨hz1,by nlinarith [sq_nonneg ‖p.2‖],by linarith⟩
  · rintro (⟨hz,hz1,hc⟩ | ⟨hz,hz1,hn⟩)
    · have hz2 : p.1^2 ≤ a^2 := (sq_le_sq₀ hz ha.le).mpr hz1
      have hc' : a^2*(p.1^2+‖p.2‖^2) ≤ p.1^2 := by nlinarith only [hc]
      refine ⟨?_,hz,hc'⟩
      nlinarith only [hc',hz2,ha2]
    · have hz0 : 0 ≤ p.1 := le_trans ha.le hz
      have hsum : p.1^2+‖p.2‖^2 ≤ 1 := by linarith
      have hz2 : a^2 ≤ p.1^2 := (sq_le_sq₀ ha.le hz0).mpr hz
      have hmul := mul_le_mul_of_nonneg_left hsum ha2.le
      exact ⟨hsum,hz0,by nlinarith only [hmul,hz2]⟩

theorem sectorSlice_zero : sectorSlice 0 = diskSolid 0 1 (fun z => 1-z^2) := by
  ext p
  constructor
  · rintro ⟨hn,hz,_⟩
    have hf : 0 ≤ 1-p.1^2 := by nlinarith [sq_nonneg ‖p.2‖]
    apply (diskSolid_mem_iff p hf).mpr
    exact ⟨⟨hz,by nlinarith [sq_nonneg ‖p.2‖]⟩,by linarith⟩
  · rintro ⟨hp,hb⟩
    have hf : 0 ≤ 1-p.1^2 := by nlinarith [hp.1,hp.2]
    have hh := (diskSolid_mem_iff (f := fun z => 1-z^2) p hf).mp ⟨hp,hb⟩
    exact ⟨by linarith [hh.2],hp.1,by simp [sq_nonneg]⟩

end
end D4Bound.SphereMeasure
