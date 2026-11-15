import D4Bound.V7CensusGramData
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem vector_data_checked : vectorDataOK = true := by decide +kernel
theorem inverse_row_0 : inverseRowOK 0 = true := by decide +kernel
theorem inverse_row_1 : inverseRowOK 1 = true := by decide +kernel
theorem inverse_row_2 : inverseRowOK 2 = true := by decide +kernel
theorem inverse_row_3 : inverseRowOK 3 = true := by decide +kernel
theorem inverse_row_4 : inverseRowOK 4 = true := by decide +kernel
end D4Bound.V7.CensusGram
