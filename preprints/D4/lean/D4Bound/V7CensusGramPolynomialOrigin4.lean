import D4Bound.V7CensusGramProjectionData
namespace D4Bound.V7.CensusGram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem projection_origin_cross_4 :
    ((List.range 34).map fun a => projectionWeightQ a *
      originOffsetQ (ray a) * projectionDualQ a 4).sum =
    ((List.range 5).map fun k => projectionGramQ 4 k * projectionOffsetQ k).sum := by
  decide +kernel
end D4Bound.V7.CensusGram
