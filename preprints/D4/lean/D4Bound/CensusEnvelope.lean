import D4Bound.CensusCheck

/-! Sound composition of the exact census envelope. The maximum is taken over
the projection floor and all twelve affine floors, before adding the spherical
surplus. This lemma preserves that order and does not assert the analytic
inequalities supplied as its inputs. -/
namespace D4Bound.CensusArithmetic
noncomputable section

def countPart (v : Counts) : ℝ :=
  (quadratic countCoeffs v : ℝ) / (denominator : ℝ)

def projectionPart (v : Counts) : ℝ :=
  ((quadratic totalCoeffs v - quadratic countCoeffs v : ℤ) : ℝ) /
    (denominator : ℝ)

def surplusPart (v : Counts) : ℝ :=
  (surplusNumerators[5*v.n4+first v-1]! : ℝ) / (denominator : ℝ)

theorem lower_le_of_components (v : Counts) (G S : ℝ)
    (hprojection : projectionPart v ≤ G)
    (hplanes : ∀ c ∈ planeCoeffs, (affine c v : ℝ)/(denominator : ℝ) ≤ G)
    (hsurplus : surplusPart v ≤ S) :
    (lower v : ℝ) ≤ G + countPart v + S := by
  have hinit : (quadratic totalCoeffs v : ℝ)/(denominator : ℝ) ≤
      G + countPart v := by
    dsimp only [projectionPart] at hprojection
    rw [Int.cast_sub,sub_div] at hprojection
    dsimp only [countPart]
    linarith
  have hradial :
      ((planeCoeffs.foldl (fun acc c => max acc (quadratic countCoeffs v + affine c v))
        (quadratic totalCoeffs v) : ℤ) : ℝ)/(denominator : ℝ) ≤
          G + countPart v := by
    apply Array.foldl_induction (motive := fun _ (b : ℤ) =>
      (b : ℝ)/(denominator : ℝ) ≤ G + countPart v) hinit
    intro i b hb
    have hc := hplanes planeCoeffs[i] (Array.getElem_mem i.isLt)
    rcases le_total b (quadratic countCoeffs v + affine planeCoeffs[i] v) with h | h
    · rw [max_eq_right h,Int.cast_add,add_div]
      dsimp only [countPart] at hb ⊢
      linarith
    · rw [max_eq_left h]
      exact hb
  have he : (lower v : ℝ) =
      ((planeCoeffs.foldl (fun acc c => max acc (quadratic countCoeffs v + affine c v))
        (quadratic totalCoeffs v) : ℤ) : ℝ)/(denominator : ℝ) + surplusPart v := by
    unfold lower numerator surplusPart
    push_cast
    ring
  rw [he]
  exact add_le_add hradial hsurplus

end
end D4Bound.CensusArithmetic
