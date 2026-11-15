import D4Bound.V7Energy
import D4Bound.ScalarCheck

/-! The two original V7 spherical components are exactly one common scalar
energy. Every coefficient is taken from the actual published V7 data. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.V7
noncomputable section
open Classical

def sphericalNormalization : ℝ := (14871048439109842089/2500000000000000000000)

def sphericalBound : ℝ := (24011149331270334059543053650135728526049/4444400000000000000000000000000000000000000)

def sphericalPower : List ℤ := [503094476623373013684556085102656, -3911640796020921586369537781435445, -4752677403576860266850864061172440, 11329741321455865370856995534893560, 46725802219866100947929827366006800, 162055715747339395778697078774339744, 79415407713162081273424843115393280, -591209593959639941244609008991560928, -871258986159490555638042391597359360, 137806689389715317127113243547765504, 829628737269853120883189835279805440, 287995818377832787905923217203466240, -77748469483188104038106958756741120]

def sphericalPowerDen : ℤ := 29774518708579010784217800000000000

def sphericalScalar (t : ℝ) : ℝ := evalZ sphericalPower t / sphericalPowerDen

theorem sphericalNormalization_pos : 0 < sphericalNormalization := by norm_num [sphericalNormalization]

lemma sphericalU0 (t : ℝ) : chebU 0 t = (1+t*0) := by

  simp [chebU] <;> ring

lemma sphericalU1 (t : ℝ) : chebU 1 t = (0+t*(2+t*0)) := by

  simp [chebU] <;> ring

lemma sphericalU2 (t : ℝ) : chebU 2 t = (-1+t*(0+t*(4+t*0))) := by

  rw [chebU,sphericalU1,sphericalU0]
  ring

lemma sphericalU3 (t : ℝ) : chebU 3 t = (0+t*(-4+t*(0+t*(8+t*0)))) := by

  rw [chebU,sphericalU2,sphericalU1]
  ring

lemma sphericalU4 (t : ℝ) : chebU 4 t = (1+t*(0+t*(-12+t*(0+t*(16+t*0))))) := by

  rw [chebU,sphericalU3,sphericalU2]
  ring

lemma sphericalU5 (t : ℝ) : chebU 5 t = (0+t*(6+t*(0+t*(-32+t*(0+t*(32+t*0)))))) := by

  rw [chebU,sphericalU4,sphericalU3]
  ring

lemma sphericalU6 (t : ℝ) : chebU 6 t = (-1+t*(0+t*(24+t*(0+t*(-80+t*(0+t*(64+t*0))))))) := by

  rw [chebU,sphericalU5,sphericalU4]
  ring

lemma sphericalU7 (t : ℝ) : chebU 7 t = (0+t*(-8+t*(0+t*(80+t*(0+t*(-192+t*(0+t*(128+t*0)))))))) := by

  rw [chebU,sphericalU6,sphericalU5]
  ring

lemma sphericalU8 (t : ℝ) : chebU 8 t = (1+t*(0+t*(-40+t*(0+t*(240+t*(0+t*(-448+t*(0+t*(256+t*0))))))))) := by

  rw [chebU,sphericalU7,sphericalU6]
  ring

lemma sphericalU9 (t : ℝ) : chebU 9 t = (0+t*(10+t*(0+t*(-160+t*(0+t*(672+t*(0+t*(-1024+t*(0+t*(512+t*0)))))))))) := by

  rw [chebU,sphericalU8,sphericalU7]
  ring

lemma sphericalU10 (t : ℝ) : chebU 10 t = (-1+t*(0+t*(60+t*(0+t*(-560+t*(0+t*(1792+t*(0+t*(-2304+t*(0+t*(1024+t*0))))))))))) := by

  rw [chebU,sphericalU9,sphericalU8]
  ring

lemma sphericalU11 (t : ℝ) : chebU 11 t = (0+t*(-12+t*(0+t*(280+t*(0+t*(-1792+t*(0+t*(4608+t*(0+t*(-5120+t*(0+t*(2048+t*0)))))))))))) := by

  rw [chebU,sphericalU10,sphericalU9]
  ring

lemma sphericalU12 (t : ℝ) : chebU 12 t = (1+t*(0+t*(-84+t*(0+t*(1120+t*(0+t*(-5376+t*(0+t*(11520+t*(0+t*(-11264+t*(0+t*(4096+t*0))))))))))))) := by

  rw [chebU,sphericalU11,sphericalU10]
  ring

theorem sphericalLinear_eq (r : ℝ) :
    sphericalLinear r = sphericalBound * (if r ≤ R5 then 1 else 0)/2 := by
  simp only [sphericalLinear,sphericalRays,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  norm_num [indicator,R5,sphericalBound]
  split_ifs <;> norm_num

theorem sphericalPair_eq (r s t : ℝ) :
    sphericalPair r s t =
      -sphericalNormalization*(if r ≤ R5 then 1 else 0)*(if s ≤ R5 then 1 else 0)*sphericalScalar t := by

  norm_num [sphericalPair,sphericalRays,indicator,R5,zonal,sphericalU0, sphericalU1, sphericalU2, sphericalU3, sphericalU4, sphericalU5, sphericalU6, sphericalU7, sphericalU8, sphericalU9, sphericalU10, sphericalU11, sphericalU12, sphericalNormalization,sphericalScalar,sphericalPower,sphericalPowerDen,evalZ,List.range_succ]
  split_ifs <;> ring


theorem spherical_energy_identity (X : Finset E4) :
    sphericalEnergy X = sphericalBound * (nearCount X : ℝ) - sphericalNormalization *
      ∑ x ∈ X.filter (fun x => ‖x‖ ≤ R5),
        ∑ y ∈ X.filter (fun y => ‖y‖ ≤ R5), sphericalScalar (⟪x,y⟫/(‖x‖*‖y‖)) := by
  have hlin : 2*∑ x ∈ X, sphericalLinear ‖x‖ = sphericalBound*(nearCount X:ℝ) := by
    simp_rw [sphericalLinear_eq]
    have hc : (∑ x ∈ X, (if ‖x‖ ≤ R5 then (1:ℝ) else 0)) = nearCount X := by
      simp [nearCount,countWithin,Finset.sum_boole]
    simp only [← Finset.sum_div,← Finset.mul_sum]
    rw [hc]
    ring
  have hpair : (∑ x ∈ X, ∑ y ∈ X, sphericalPair ‖x‖ ‖y‖ (⟪x,y⟫/(‖x‖*‖y‖))) =
      -sphericalNormalization * ∑ x ∈ X.filter (fun x => ‖x‖ ≤ R5),
        ∑ y ∈ X.filter (fun y => ‖y‖ ≤ R5), sphericalScalar (⟪x,y⟫/(‖x‖*‖y‖)) := by
    simp_rw [sphericalPair_eq]
    simp only [Finset.sum_filter,Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : ‖x‖ ≤ R5
    · simp only [hx,ite_true,mul_one,Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : ‖y‖ ≤ R5 <;> simp [hy]
    · simp [hx]
  unfold sphericalEnergy radialEnergy
  rw [hlin,hpair]
  ring

#print axioms spherical_energy_identity
end
end D4Bound.V7
