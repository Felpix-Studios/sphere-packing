import D4Bound.V7SphericalSurplusBase
import D4Bound.SphericalSurplusBounds2
import D4Bound.SphericalSurplusTable
import D4Bound.V7SphericalTransfer

/-! The actual spherical surplus in the complete finite census. Triangle
certificate conclusions are explicit inputs until the full replay supplies them. -/
set_option maxHeartbeats 0
set_option Elab.async false
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical
open SphericalSurplusBounds

theorem fixed25_surplus (hT : B2.TriangleSign) (X : Finset E4) (hX : Admissible X)
    (hN : nearCount X=25) (hj : firstRadius X≤4) :
    (SphericalSurplusTable.credit2 (nearCount X):ℝ) ≤ sphericalEnergy X := by
  unfold SphericalSurplusTable.credit2
  push_cast
  apply max_le
  · have hb := spherical_energy_ge_of_upper X hX R4 (103/200)
      ((nearCount X:ℝ)*B2.repairedB) (by norm_num [R4]) (by norm_num [R4])
      (all_le_R4_of_first_le_four hj) (fun x hx hs => B2.repaired_upper_of_triangle hT hN x hx hs)
    convert hb using 2 <;>
      norm_num [SphericalSurplusTable.B,SphericalSurplusTable.W,SphericalSurplusTable.repaired2,
        sphericalBound,sphericalNormalization,B2.repairedB] <;> first | rfl | ring
  · have hb := spherical_energy_ge_of_upper X hX R4 (103/200)
      ((nearCount X:ℝ)*B2.rawB+(SphericalSurplusSign.eta2:ℝ)*(nearCount X)*(nearCount X-1)+
        (SphericalSurplusSign.epsilon2:ℝ)*(nearCount X)*(nearCount X-1)*(nearCount X-2))
      (by norm_num [R4]) (by norm_num [R4]) (all_le_R4_of_first_le_four hj)
      (fun x hx hs => B2.raw_upper_of_triangle hT hN x hx hs)
    convert hb using 2 <;>
      norm_num [SphericalSurplusTable.B,SphericalSurplusTable.W,SphericalSurplusTable.raw2,
        SphericalSurplusTable.eta2,SphericalSurplusTable.epsilon2,
        SphericalSurplusSign.eta2,SphericalSurplusSign.epsilon2,
        sphericalBound,sphericalNormalization,B2.rawB] <;> first | rfl | ring

theorem surplus_floor_of_triangles (h0 : B0.TriangleSign) (h1 : B1.TriangleSign)
    (h2 : B2.TriangleSign) (X : Finset E4) (hX : Admissible X) (hC : InCountDomain X) :
    CensusArithmetic.surplusPart (CensusArithmetic.ofNeighbourhood X) ≤ sphericalEnergy X := by
  have hv := CensusArithmetic.ofNeighbourhood_valid hC
  have hN : nearCount X ≤ 26 := hv.2.2.2.2.2.2.1
  have hu := uniform_surplus h1 X hX hN
  have hcredit : 0 ≤ (SphericalSurplusTable.credit1 (nearCount X):ℝ) := by
    unfold SphericalSurplusTable.credit1
    push_cast
    apply le_trans _ (le_max_left _ _)
    apply mul_nonneg (Nat.cast_nonneg _)
    norm_num [SphericalSurplusTable.B,SphericalSurplusTable.W,SphericalSurplusTable.repaired1]
  apply le_trans (SphericalSurplusTable.surplus_part_le _ hN)
  apply SphericalSurplusTable.available_le
  · exact hcredit.trans hu
  · exact hu
  · intro hn hj
    have hj1 := SphericalSurplusTable.first_pos (CensusArithmetic.ofNeighbourhood X)
    have hh : firstRadius X=1 := by
      change firstRadius X≤1 at hj
      change 1≤firstRadius X at hj1
      omega
    exact fixed24_surplus h0 X hX hn hh
  · intro hn hj
    exact fixed25_surplus h2 X hX hn hj

#print axioms surplus_floor_of_triangles
end
end D4Bound.V7
