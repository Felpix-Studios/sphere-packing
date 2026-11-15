import D4Bound.V7CensusGramOriginSound
import D4Bound.V7CensusGramCheck0
import D4Bound.V7CensusGramCheck1
import D4Bound.V7CensusGramCheck2
import D4Bound.V7CensusGramCheck3
import D4Bound.V7CensusGramCheck4
import D4Bound.V7CensusGramCheck5
import D4Bound.V7CensusGramCheck6
import D4Bound.V7CensusGramCheck7
import D4Bound.CensusEnvelope
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def projectionWeightQ (i : ℕ) : ℚ := (ray i).weight/gramDenominator
def projectionDualQ (i j : ℕ) : ℚ := ((dualNums[i]!)[j]! : ℚ)/(dualDen : ℚ)
def projectionGramQ (j k : ℕ) : ℚ := ((inverseNums[j]!)[k]! : ℚ)/(inverseDen : ℚ)
def projectionOffsetQ (j : ℕ) : ℚ := (countOffsetNums[j]! : ℚ)/(countOffsetDen : ℚ)

def projectionTargetQ (j : ℕ) : List ℚ :=
  (List.range 49).map fun k =>
    ((List.range 5).map fun l => if k/7 ≤ l then projectionGramQ l j else 0).sum

theorem range_rows_checked (k : ℕ) (hk : k < 49) : rangeRowOK k = true := by
  interval_cases k
  · exact range_row_0
  · exact range_row_1
  · exact range_row_2
  · exact range_row_3
  · exact range_row_4
  · exact range_row_5
  · exact range_row_6
  · exact range_row_7
  · exact range_row_8
  · exact range_row_9
  · exact range_row_10
  · exact range_row_11
  · exact range_row_12
  · exact range_row_13
  · exact range_row_14
  · exact range_row_15
  · exact range_row_16
  · exact range_row_17
  · exact range_row_18
  · exact range_row_19
  · exact range_row_20
  · exact range_row_21
  · exact range_row_22
  · exact range_row_23
  · exact range_row_24
  · exact range_row_25
  · exact range_row_26
  · exact range_row_27
  · exact range_row_28
  · exact range_row_29
  · exact range_row_30
  · exact range_row_31
  · exact range_row_32
  · exact range_row_33
  · exact range_row_34
  · exact range_row_35
  · exact range_row_36
  · exact range_row_37
  · exact range_row_38
  · exact range_row_39
  · exact range_row_40
  · exact range_row_41
  · exact range_row_42
  · exact range_row_43
  · exact range_row_44
  · exact range_row_45
  · exact range_row_46
  · exact range_row_47
  · exact range_row_48

theorem inverse_rows_checked (j : ℕ) (hj : j < 5) : inverseRowOK j = true := by
  interval_cases j
  · exact inverse_row_0
  · exact inverse_row_1
  · exact inverse_row_2
  · exact inverse_row_3
  · exact inverse_row_4

theorem ray_weight_checked (i : ℕ) (hi : i < 34) :
    (rayWeights[i]! : ℚ) = (ray i).weight := by
  have h := vector_data_checked
  simp only [vectorDataOK, List.all_eq_true, decide_eq_true_eq] at h
  exact (h i (List.mem_range.mpr hi)).1

theorem ray_vector_checked (i k : ℕ) (hi : i < 34) (hk : k < 49) :
    ((rayVectors[i]!)[k]! : ℚ) = (ray i).vector.getD k 0 := by
  have h := vector_data_checked
  simp only [vectorDataOK, List.all_eq_true, decide_eq_true_eq] at h
  exact (h i (List.mem_range.mpr hi)).2 k (List.mem_range.mpr hk)

theorem gramRays0_range : (List.range 34).map ray = gramRays0 := by rfl

theorem range_integer (k j : ℕ) (hk : k < 49) (hj : j < 5) :
    ((List.range 34).map fun i => rayWeights[i]!*(rayVectors[i]!)[k]!*(dualNums[i]!)[j]!).sum * inverseDen =
    gramDen*dualDen*((List.range 5).map fun l => if k/7 ≤ l then (inverseNums[l]!)[j]! else 0).sum := by
  have h := range_rows_checked k hk
  simp only [rangeRowOK,List.all_eq_true,decide_eq_true_eq] at h
  exact h j (List.mem_range.mpr hj)

theorem inverse_integer (j k : ℕ) (hj : j < 5) (hk : k < 5) :
    ((List.range 34).map fun i => rayWeights[i]!*(dualNums[i]!)[j]!*(dualNums[i]!)[k]!).sum * inverseDen =
      gramDen*dualDen^2*(inverseNums[j]!)[k]! := by
  have h := inverse_rows_checked j hj
  simp only [inverseRowOK,List.all_eq_true,decide_eq_true_eq] at h
  exact h k (List.mem_range.mpr hk)

end D4Bound.V7.CensusGram
