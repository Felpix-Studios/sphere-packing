import D4Bound.SphericalSurplusSignPhysical0

import D4Bound.SphericalSurplusSignPower0Data

import D4Bound.SphericalSurplusSignPowerAlgebra16

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign

open SphericalSign Bernstein16

def rawPower0 : Tensor := powerTensor physicalNum0

theorem physicalNum0_bounded : bounded3 physicalNum0 := by decide +kernel

theorem rawPower0_correct (a b t : ℝ) :
    powerEv rawPower0 a b t=40320*(featureDen0:ℝ)^2*kernel0 a b t := by
  rw [rawPower0,←eval3_powerTensor physicalNum0 physicalNum0_bounded,physicalNum0_correct]

theorem repairPower0_row0 : ∀ j k, repairPower0 0 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 0 j k := by decide +kernel

theorem repairPower0_row1 : ∀ j k, repairPower0 1 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 1 j k := by decide +kernel

theorem repairPower0_row2 : ∀ j k, repairPower0 2 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 2 j k := by decide +kernel

theorem repairPower0_row3 : ∀ j k, repairPower0 3 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 3 j k := by decide +kernel

theorem repairPower0_row4 : ∀ j k, repairPower0 4 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 4 j k := by decide +kernel

theorem repairPower0_row5 : ∀ j k, repairPower0 5 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 5 j k := by decide +kernel

theorem repairPower0_row6 : ∀ j k, repairPower0 6 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 6 j k := by decide +kernel

theorem repairPower0_row7 : ∀ j k, repairPower0 7 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 7 j k := by decide +kernel

theorem repairPower0_row8 : ∀ j k, repairPower0 8 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 8 j k := by decide +kernel

theorem repairPower0_row9 : ∀ j k, repairPower0 9 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 9 j k := by decide +kernel

theorem repairPower0_row10 : ∀ j k, repairPower0 10 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 10 j k := by decide +kernel

theorem repairPower0_row11 : ∀ j k, repairPower0 11 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 11 j k := by decide +kernel

theorem repairPower0_row12 : ∀ j k, repairPower0 12 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 12 j k := by decide +kernel

theorem repairPower0_row13 : ∀ j k, repairPower0 13 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 13 j k := by decide +kernel

theorem repairPower0_row14 : ∀ j k, repairPower0 14 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 14 j k := by decide +kernel

theorem repairPower0_row15 : ∀ j k, repairPower0 15 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 15 j k := by decide +kernel

theorem repairPower0_row16 : ∀ j k, repairPower0 16 j k=(addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000))) 16 j k := by decide +kernel

theorem repairPower0_eq : repairPower0=addTensor (scaleTensor 500000 (cyclicTensor rawPower0)) (constTensor (-3752508216899758088883195116387914330793770868737604028583047396668846127668896194252532228971473280000000000000000000)) := by
  funext i j k
  fin_cases i
  · exact repairPower0_row0 j k
  · exact repairPower0_row1 j k
  · exact repairPower0_row2 j k
  · exact repairPower0_row3 j k
  · exact repairPower0_row4 j k
  · exact repairPower0_row5 j k
  · exact repairPower0_row6 j k
  · exact repairPower0_row7 j k
  · exact repairPower0_row8 j k
  · exact repairPower0_row9 j k
  · exact repairPower0_row10 j k
  · exact repairPower0_row11 j k
  · exact repairPower0_row12 j k
  · exact repairPower0_row13 j k
  · exact repairPower0_row14 j k
  · exact repairPower0_row15 j k
  · exact repairPower0_row16 j k

theorem repairPower0_correct (a b t : ℝ) :
    powerEv repairPower0 a b t=(repairDen0:ℝ)*
      (kernel0 a b t+kernel0 a t b+kernel0 b t a-3*(epsilon0:ℝ)) := by
  rw [repairPower0_eq,powerEv_add,powerEv_scale,powerEv_cyclic,powerEv_const]
  simp only [rawPower0_correct]
  norm_num [repairDen0,featureDen0,epsilon0]
  ring

#print axioms repairPower0_correct

end D4Bound.SphericalSurplusSign
