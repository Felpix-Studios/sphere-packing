import D4Bound.V7CensusGramOrigin
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem origin_row_0 : originRowOK 0 = true := by decide +kernel
theorem origin_row_1 : originRowOK 1 = true := by decide +kernel
theorem origin_row_2 : originRowOK 2 = true := by decide +kernel
theorem origin_row_3 : originRowOK 3 = true := by decide +kernel
theorem origin_row_4 : originRowOK 4 = true := by decide +kernel
theorem origin_row_5 : originRowOK 5 = true := by decide +kernel
theorem origin_row_6 : originRowOK 6 = true := by decide +kernel
end D4Bound.V7.CensusGram
