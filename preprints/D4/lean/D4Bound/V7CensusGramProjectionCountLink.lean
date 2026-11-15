import D4Bound.V7CensusGramProjectionEnergy
import D4Bound.V7CensusGramPolynomialBasic
namespace D4Bound.V7.CensusGram
noncomputable section
open Finset CensusArithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem projection_count_coordinate (X : Finset E4) (j : ℕ) (hj : j < 5) :
    countWithin X ((breaks.getD (j+1) 0 : ℚ) : ℝ) = countsAt (ofNeighbourhood X) j := by
  interval_cases j <;>
    norm_num [breaks,countsAt,ofNeighbourhood,nearCount,R1,R2,R3,R4,R5]

theorem projection_counts_matrix (X : Finset E4) :
    matrixProjection (fun j k => (projectionGramQ j k : ℝ))
      (fun j => (projectionOffsetQ j : ℝ))
      (fun j => (countsAt (ofNeighbourhood X) j : ℝ)) =
      ∑ j : Fin 5, ∑ k : Fin 5, projectionCounts X j *
        (projectionGramQ j k : ℝ)*projectionCounts X k := by
  unfold matrixProjection
  simp_rw [← fin5_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [projectionCounts,projection_count_coordinate X j j.isLt,
    projection_count_coordinate X k k.isLt]

end
end D4Bound.V7.CensusGram
