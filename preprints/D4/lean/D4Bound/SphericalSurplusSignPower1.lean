import D4Bound.SphericalSurplusSignPhysical1

import D4Bound.SphericalSurplusSignPower1Data

import D4Bound.SphericalSurplusSignPowerAlgebra16

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign

open SphericalSign Bernstein16

def rawPower1 : Tensor := powerTensor physicalNum1

theorem physicalNum1_bounded : bounded3 physicalNum1 := by decide +kernel

theorem rawPower1_correct (a b t : ℝ) :
    powerEv rawPower1 a b t=40320*(featureDen1:ℝ)^2*kernel1 a b t := by
  rw [rawPower1,←eval3_powerTensor physicalNum1 physicalNum1_bounded,physicalNum1_correct]

theorem repairPower1_row0 : ∀ j k, repairPower1 0 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 0 j k := by decide +kernel

theorem repairPower1_row1 : ∀ j k, repairPower1 1 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 1 j k := by decide +kernel

theorem repairPower1_row2 : ∀ j k, repairPower1 2 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 2 j k := by decide +kernel

theorem repairPower1_row3 : ∀ j k, repairPower1 3 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 3 j k := by decide +kernel

theorem repairPower1_row4 : ∀ j k, repairPower1 4 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 4 j k := by decide +kernel

theorem repairPower1_row5 : ∀ j k, repairPower1 5 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 5 j k := by decide +kernel

theorem repairPower1_row6 : ∀ j k, repairPower1 6 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 6 j k := by decide +kernel

theorem repairPower1_row7 : ∀ j k, repairPower1 7 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 7 j k := by decide +kernel

theorem repairPower1_row8 : ∀ j k, repairPower1 8 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 8 j k := by decide +kernel

theorem repairPower1_row9 : ∀ j k, repairPower1 9 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 9 j k := by decide +kernel

theorem repairPower1_row10 : ∀ j k, repairPower1 10 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 10 j k := by decide +kernel

theorem repairPower1_row11 : ∀ j k, repairPower1 11 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 11 j k := by decide +kernel

theorem repairPower1_row12 : ∀ j k, repairPower1 12 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 12 j k := by decide +kernel

theorem repairPower1_row13 : ∀ j k, repairPower1 13 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 13 j k := by decide +kernel

theorem repairPower1_row14 : ∀ j k, repairPower1 14 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 14 j k := by decide +kernel

theorem repairPower1_row15 : ∀ j k, repairPower1 15 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 15 j k := by decide +kernel

theorem repairPower1_row16 : ∀ j k, repairPower1 16 j k=(addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000))) 16 j k := by decide +kernel

theorem repairPower1_eq : repairPower1=addTensor (scaleTensor 250000 (cyclicTensor rawPower1)) (constTensor (-4445484888898867721876244012562560000000000000000000)) := by
  funext i j k
  fin_cases i
  · exact repairPower1_row0 j k
  · exact repairPower1_row1 j k
  · exact repairPower1_row2 j k
  · exact repairPower1_row3 j k
  · exact repairPower1_row4 j k
  · exact repairPower1_row5 j k
  · exact repairPower1_row6 j k
  · exact repairPower1_row7 j k
  · exact repairPower1_row8 j k
  · exact repairPower1_row9 j k
  · exact repairPower1_row10 j k
  · exact repairPower1_row11 j k
  · exact repairPower1_row12 j k
  · exact repairPower1_row13 j k
  · exact repairPower1_row14 j k
  · exact repairPower1_row15 j k
  · exact repairPower1_row16 j k

theorem repairPower1_correct (a b t : ℝ) :
    powerEv repairPower1 a b t=(repairDen1:ℝ)*
      (kernel1 a b t+kernel1 a t b+kernel1 b t a-3*(epsilon1:ℝ)) := by
  rw [repairPower1_eq,powerEv_add,powerEv_scale,powerEv_cyclic,powerEv_const]
  simp only [rawPower1_correct]
  norm_num [repairDen1,featureDen1,epsilon1]
  ring

#print axioms repairPower1_correct

end D4Bound.SphericalSurplusSign
