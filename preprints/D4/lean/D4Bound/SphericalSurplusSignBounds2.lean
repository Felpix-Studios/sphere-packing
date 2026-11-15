-- Exact constants are tied to rays and scalar polynomial below.

import D4Bound.SphericalSurplusSignData2

import D4Bound.SphericalConcreteBasic

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign

open SphericalSign SphericalConcrete

def rawBound2 : ℚ := 32684678624403525301964627843417351227/37180967418305458022250000000000000000

def repairedBound2 : ℚ := 32781066933107189220742908478457351227/37180967418305458022250000000000000000

def maxCount2 : ℕ := 25

def repairDiagonal2 : ℚ := 133770012193/4999950000

theorem originNumerator2_exact : originNumerator rays2 = 8141351166815190540 := by
  decide +kernel

theorem rawBound2_correct : g2 1 + origin2 = (rawBound2:ℝ) := by
  unfold origin2
  rw [origin_eq, originNumerator2_exact]
  norm_num [g2,scalarPower2,scalarPowerDen2,evalZ,originDen2,countM2,
    v2,vNum2,b2,bNum2,rawBound2]

theorem repairedBound2_correct :
    (rawBound2:ℝ) + ((maxCount2:ℝ)-1) *
      ((eta2:ℝ) + (epsilon2:ℝ)*(repairDiagonal2:ℝ)) = (repairedBound2:ℝ) := by
  norm_num [rawBound2,maxCount2,eta2,epsilon2,repairDiagonal2,repairedBound2]

#print axioms rawBound2_correct

#print axioms repairedBound2_correct

end D4Bound.SphericalSurplusSign
