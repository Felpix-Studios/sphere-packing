import D4Bound.SphericalSurplusSignPhysical2

import D4Bound.SphericalSurplusSignPower2Data

import D4Bound.SphericalSurplusSignPowerAlgebra16

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign

open SphericalSign Bernstein16

def rawPower2 : Tensor := powerTensor physicalNum2

theorem physicalNum2_bounded : bounded3 physicalNum2 := by decide +kernel

theorem rawPower2_correct (a b t : ℝ) :
    powerEv rawPower2 a b t=40320*(featureDen2:ℝ)^2*kernel2 a b t := by
  rw [rawPower2,←eval3_powerTensor physicalNum2 physicalNum2_bounded,physicalNum2_correct]

theorem repairPower2_row0 : ∀ j k, repairPower2 0 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 0 j k := by decide +kernel

theorem repairPower2_row1 : ∀ j k, repairPower2 1 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 1 j k := by decide +kernel

theorem repairPower2_row2 : ∀ j k, repairPower2 2 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 2 j k := by decide +kernel

theorem repairPower2_row3 : ∀ j k, repairPower2 3 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 3 j k := by decide +kernel

theorem repairPower2_row4 : ∀ j k, repairPower2 4 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 4 j k := by decide +kernel

theorem repairPower2_row5 : ∀ j k, repairPower2 5 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 5 j k := by decide +kernel

theorem repairPower2_row6 : ∀ j k, repairPower2 6 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 6 j k := by decide +kernel

theorem repairPower2_row7 : ∀ j k, repairPower2 7 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 7 j k := by decide +kernel

theorem repairPower2_row8 : ∀ j k, repairPower2 8 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 8 j k := by decide +kernel

theorem repairPower2_row9 : ∀ j k, repairPower2 9 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 9 j k := by decide +kernel

theorem repairPower2_row10 : ∀ j k, repairPower2 10 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 10 j k := by decide +kernel

theorem repairPower2_row11 : ∀ j k, repairPower2 11 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 11 j k := by decide +kernel

theorem repairPower2_row12 : ∀ j k, repairPower2 12 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 12 j k := by decide +kernel

theorem repairPower2_row13 : ∀ j k, repairPower2 13 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 13 j k := by decide +kernel

theorem repairPower2_row14 : ∀ j k, repairPower2 14 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 14 j k := by decide +kernel

theorem repairPower2_row15 : ∀ j k, repairPower2 15 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 15 j k := by decide +kernel

theorem repairPower2_row16 : ∀ j k, repairPower2 16 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000))) 16 j k := by decide +kernel

theorem repairPower2_eq : repairPower2=addTensor (scaleTensor 250000 (cyclicTensor rawPower2)) (constTensor (-610553653257806695594620917281184273318828160000000000000000000)) := by
  funext i j k
  fin_cases i
  · exact repairPower2_row0 j k
  · exact repairPower2_row1 j k
  · exact repairPower2_row2 j k
  · exact repairPower2_row3 j k
  · exact repairPower2_row4 j k
  · exact repairPower2_row5 j k
  · exact repairPower2_row6 j k
  · exact repairPower2_row7 j k
  · exact repairPower2_row8 j k
  · exact repairPower2_row9 j k
  · exact repairPower2_row10 j k
  · exact repairPower2_row11 j k
  · exact repairPower2_row12 j k
  · exact repairPower2_row13 j k
  · exact repairPower2_row14 j k
  · exact repairPower2_row15 j k
  · exact repairPower2_row16 j k

theorem repairPower2_correct (a b t : ℝ) :
    powerEv repairPower2 a b t=(repairDen2:ℝ)*
      (kernel2 a b t+kernel2 a t b+kernel2 b t a-3*(epsilon2:ℝ)) := by
  rw [repairPower2_eq,powerEv_add,powerEv_scale,powerEv_cyclic,powerEv_const]
  simp only [rawPower2_correct]
  norm_num [repairDen2,featureDen2,epsilon2]
  ring

#print axioms repairPower2_correct

end D4Bound.SphericalSurplusSign
