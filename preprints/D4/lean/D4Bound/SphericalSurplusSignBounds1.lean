-- Exact constants are tied to rays and scalar polynomial below.

import D4Bound.SphericalSurplusSignData1

import D4Bound.SphericalConcreteBasic

set_option maxHeartbeats 0

set_option maxRecDepth 20000

set_option Elab.async false

namespace D4Bound.SphericalSurplusSign

open SphericalSign SphericalConcrete

def rawBound1 : ℚ := 65914448509406451575062474686557247029/74361934836610916044500000000000000000

def repairedBound1 : ℚ := 7346139720652490896946358445506360781/8262437204067879560500000000000000000

def maxCount1 : ℕ := 26

def repairDiagonal1 : ℚ := 133770012193/4999950000

theorem originNumerator1_exact : originNumerator rays1 = 665418194099172922 := by
  decide +kernel

theorem rawBound1_correct : g1 1 + origin1 = (rawBound1:ℝ) := by
  unfold origin1
  rw [origin_eq, originNumerator1_exact]
  norm_num [g1,scalarPower1,scalarPowerDen1,evalZ,originDen1,countM1,
    v1,vNum1,b1,bNum1,rawBound1]

theorem repairedBound1_correct :
    (rawBound1:ℝ) + ((maxCount1:ℝ)-1) *
      ((eta1:ℝ) + (epsilon1:ℝ)*(repairDiagonal1:ℝ)) = (repairedBound1:ℝ) := by
  norm_num [rawBound1,maxCount1,eta1,epsilon1,repairDiagonal1,repairedBound1]

#print axioms rawBound1_correct

#print axioms repairedBound1_correct

end D4Bound.SphericalSurplusSign
