import D4Bound.V7CensusGramData
namespace D4Bound.V7.CensusGram
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem range_row_0 : rangeRowOK 0 = true := by decide +kernel
theorem range_row_1 : rangeRowOK 1 = true := by decide +kernel
theorem range_row_2 : rangeRowOK 2 = true := by decide +kernel
theorem range_row_3 : rangeRowOK 3 = true := by decide +kernel
theorem range_row_4 : rangeRowOK 4 = true := by decide +kernel
theorem range_row_5 : rangeRowOK 5 = true := by decide +kernel
theorem range_row_6 : rangeRowOK 6 = true := by decide +kernel
end D4Bound.V7.CensusGram
