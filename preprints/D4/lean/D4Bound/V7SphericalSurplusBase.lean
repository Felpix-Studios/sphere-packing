import D4Bound.SphericalSurplusBounds0
import D4Bound.SphericalSurplusBounds1
import D4Bound.SphericalSurplusTable
import D4Bound.V7SphericalTransfer

/-! Transfer the bounded26 and fixed24 ANGULAR energy bounds to their exact
census credits. Physical triangle signs remain explicit until full replay. -/
set_option maxHeartbeats 0
set_option Elab.async false
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical
open SphericalSurplusBounds

theorem uniform_surplus (hT : B1.TriangleSign) (X : Finset E4) (hX : Admissible X)
    (hN : nearCount X ≤ 26) :
    (SphericalSurplusTable.credit1 (nearCount X):ℝ) ≤ sphericalEnergy X := by
  unfold SphericalSurplusTable.credit1
  push_cast
  apply max_le
  · have hb := spherical_energy_ge_of_upper X hX R5 (21/40)
      ((nearCount X:ℝ)*B1.repairedB) (by norm_num [R5]) (by norm_num [R5])
      (fun _ _ h => h) (fun x hx hs => B1.repaired_upper_of_triangle hT hN x hx hs)
    convert hb using 2 <;>
      norm_num [SphericalSurplusTable.B,SphericalSurplusTable.W,SphericalSurplusTable.repaired1,
        sphericalBound,sphericalNormalization,B1.repairedB] <;> first | rfl | ring
  · have hb := spherical_energy_ge_of_upper X hX R5 (21/40)
      ((nearCount X:ℝ)*B1.rawB+(SphericalSurplusSign.eta1:ℝ)*(nearCount X)*(nearCount X-1)+
        (SphericalSurplusSign.epsilon1:ℝ)*(nearCount X)*(nearCount X-1)*(nearCount X-2))
      (by norm_num [R5]) (by norm_num [R5]) (fun _ _ h => h)
      (fun x hx hs => B1.raw_upper_of_triangle hT hN x hx hs)
    convert hb using 2 <;>
      norm_num [SphericalSurplusTable.B,SphericalSurplusTable.W,SphericalSurplusTable.raw1,
        SphericalSurplusTable.eta1,SphericalSurplusTable.epsilon1,
        SphericalSurplusSign.eta1,SphericalSurplusSign.epsilon1,
        sphericalBound,sphericalNormalization,B1.rawB] <;> first | rfl | ring

theorem fixed24_surplus (hT : B0.TriangleSign) (X : Finset E4) (hX : Admissible X)
    (hN : nearCount X=24) (hj : firstRadius X=1) :
    (SphericalSurplusTable.credit0 (nearCount X):ℝ) ≤ sphericalEnergy X := by
  unfold SphericalSurplusTable.credit0
  push_cast
  apply max_le
  · have hb := spherical_energy_ge_of_upper X hX R1 (251467/500000)
      ((nearCount X:ℝ)*B0.repairedB) (by norm_num [R1]) (by norm_num [R1])
      (all_le_R1 hj) (fun x hx hs => B0.repaired_upper_of_triangle hT hN x hx hs)
    convert hb using 2 <;>
      norm_num [SphericalSurplusTable.B,SphericalSurplusTable.W,SphericalSurplusTable.repaired0,
        sphericalBound,sphericalNormalization,B0.repairedB] <;> first | rfl | ring
  · have hb := spherical_energy_ge_of_upper X hX R1 (251467/500000)
      ((nearCount X:ℝ)*B0.rawB+(SphericalSurplusSign.eta0:ℝ)*(nearCount X)*(nearCount X-1)+
        (SphericalSurplusSign.epsilon0:ℝ)*(nearCount X)*(nearCount X-1)*(nearCount X-2))
      (by norm_num [R1]) (by norm_num [R1]) (all_le_R1 hj)
      (fun x hx hs => B0.raw_upper_of_triangle hT hN x hx hs)
    convert hb using 2 <;>
      norm_num [SphericalSurplusTable.B,SphericalSurplusTable.W,SphericalSurplusTable.raw0,
        SphericalSurplusTable.eta0,SphericalSurplusTable.epsilon0,
        SphericalSurplusSign.eta0,SphericalSurplusSign.epsilon0,
        sphericalBound,sphericalNormalization,B0.rawB] <;> first | rfl | ring

#print axioms uniform_surplus
#print axioms fixed24_surplus
end
end D4Bound.V7
