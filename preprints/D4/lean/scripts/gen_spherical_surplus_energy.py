"""Generate common scalar linkage for the three ANGULAR surplus certificates.
All displayed equalities are proved in Lean; this producer is not trusted.
"""
from fractions import Fraction as Q
from pathlib import Path
import json,math,argparse
HERE=Path(__file__).resolve().parent
PKG=HERE.parents[1]
TARGET=HERE.parent/'D4Bound/V7SphericalScalar.lean'
def rat(q):return f'({q.numerator}/{q.denominator})'
def add(p,q):
 r=[Q(0)]*max(len(p),len(q))
 for i,v in enumerate(p):r[i]+=v
 for i,v in enumerate(q):r[i]+=v
 return r
def horner(p,t):
 s='0'
 for c in reversed(p):s=f'({int(c)}+{t}*{s})'
 return s
def generate():
 records=[json.loads((PKG/f'verify/stage2_origin/reference/ANGULAR_{i}.json').read_text()) for i in range(3)]
 a=records[0]['accepted_combination'];W=Q(a['positive_normalization']);B=Q(a['weighted_accepted_B'])
 for r in records:assert r['accepted_combination']==a
 cs=[Q(c)/W for c in a['weighted_accepted_g']]
 U=[[Q(1)],[Q(0),Q(2)]]
 for n in range(2,len(cs)):U.append(add([0]+[2*x for x in U[-1]],[-x for x in U[-2]]))
 p=[Q(0)]
 for n,c in enumerate(cs):p=add(p,[c*v/Q(n+1) for v in U[n]])
 D=math.lcm(*(c.denominator for c in p));P=[int(c*D) for c in p]
 out=['''import D4Bound.V7Energy
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
''']
 out += [f'def sphericalNormalization : ℝ := {rat(W)}\n',f'def sphericalBound : ℝ := {rat(B)}\n',f'def sphericalPower : List ℤ := {P}\n',f'def sphericalPowerDen : ℤ := {D}\n',
  'def sphericalScalar (t : ℝ) : ℝ := evalZ sphericalPower t / sphericalPowerDen\n',
  'theorem sphericalNormalization_pos : 0 < sphericalNormalization := by norm_num [sphericalNormalization]\n']
 for k,u in enumerate(U):
  out.append(f'lemma sphericalU{k} (t : ℝ) : chebU {k} t = {horner(u,"t")} := by\n')
  if k<2:out.append('  simp [chebU] <;> ring\n')
  else:out.append(f'  rw [chebU,sphericalU{k-1},sphericalU{k-2}]\n  ring\n')
 out.append('''theorem sphericalLinear_eq (r : ℝ) :
    sphericalLinear r = sphericalBound * (if r ≤ R5 then 1 else 0)/2 := by
  simp only [sphericalLinear,sphericalRays,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  norm_num [indicator,R5,sphericalBound]
  split_ifs <;> norm_num

theorem sphericalPair_eq (r s t : ℝ) :
    sphericalPair r s t =
      -sphericalNormalization*(if r ≤ R5 then 1 else 0)*(if s ≤ R5 then 1 else 0)*sphericalScalar t := by
''')
 out.append('  norm_num [sphericalPair,sphericalRays,indicator,R5,zonal,'+', '.join(f'sphericalU{k}' for k in range(len(cs)))+', sphericalNormalization,sphericalScalar,sphericalPower,sphericalPowerDen,evalZ,List.range_succ]\n  split_ifs <;> ring\n')
 out.append('''
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
''')
 return '\n'.join(out)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();s=generate()
 if a.check:assert TARGET.read_text()==s;print('PASS: spherical common scalar source regeneration')
 else:TARGET.write_text(s);print(TARGET)
