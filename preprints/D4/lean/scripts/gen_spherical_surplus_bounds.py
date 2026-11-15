"""Instantiate both exact surplus bounds for the three published ANGULAR inputs.
Each resulting theorem still names its triangle-sign input explicitly; the
separate full tree replay supplies that input. No certificate flag is trusted.
"""
from pathlib import Path
from fractions import Fraction as Q
import json, argparse
HERE=Path(__file__).resolve().parent
PKG=HERE.parents[1]
def rat(q):return f'({q.numerator}/{q.denominator})'
def generate(i):
 r=json.loads((PKG/f'verify/stage2_origin/reference/ANGULAR_{i}.json').read_text())
 scalar=r['raw_B']; repaired=r['normalized_B'] if i==1 else r['B']
 data=(HERE.parent/f'D4Bound/SphericalSurplusSignData{i}.lean').read_text()
 # Origin numerator is reconstructed from the exact generated reduced rays.
 import re
 rays=re.findall(r'⟨(\d+),\s*(-?\d+),\s*\[', data)
 if not rays:
  raise ValueError('Unexpected ray format; inspect actual source')
 origin=sum(int(o)**2 for l,o in rays if int(l)==0)
 s=['251467/500000','21/40','103/200'][i]
 n=[24,26,25][i]
 condition=f'(hN : n = {n})' if i!=1 else '(hN : n ≤ 26)'
 countProof=f'Or.inl (by norm_num [hN,countM{i}])' if i!=1 else f'Or.inr ⟨by norm_num [b{i},bNum{i}], by norm_num [v{i},vNum{i}], by intro a; simp [F{i},correction{i},evalZ]⟩'
 hM='by exact_mod_cast hN' if i==1 else 'by norm_num [hN]'
 return f'''import D4Bound.SphericalSurplusSignPairLink{i}
import D4Bound.SphericalSurplusSignBounds{i}
import D4Bound.SphericalSurplusCompose
import D4Bound.SphericalConcreteBasic
import D4Bound.SphericalConcreteRepair26
import D4Bound.V7SphericalScalar

/-! Literal surplus instantiation. The theorem ending in `_of_triangle` exposes
exactly the remaining continuous sign statement; it is not asserted here. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Finset
open scoped RealInnerProductSpace
namespace D4Bound.SphericalSurplusBounds.B{i}
open SphericalSurplusSign SphericalSign SphereCertificate

noncomputable def rawB : ℝ := {rat(Q(scalar))}
noncomputable def repairedB : ℝ := {rat(Q(repaired))}

theorem scalar_eq (t : ℝ) : g{i} t = V7.sphericalScalar t := by rfl

theorem rawB_eq : g{i} 1 + origin{i} = rawB := by
  simpa [rawB,rawBound{i}] using rawBound{i}_correct

theorem repairedB_eq : rawB + ({n}-1)*(epsilon{i}*SphericalConcrete.C26.D+eta{i}) = repairedB := by
  norm_num [rawB,repairedB,epsilon{i},eta{i},SphericalConcrete.C26.D]

theorem repair_psd : SpherePSD SphericalConcrete.C26.T :=
  harmonic_PSD Finset.univ (fun i : Fin 24 => i.val+1) SphericalConcrete.C26.repairWeights
    (fun i _ => SphericalConcrete.C26.repair_nonneg i)

theorem floor {{n : ℕ}} {condition} (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1) :
    ∀ i, 0 ≤ SphereLocal.energy (anchorKernel kernel{i} x) (anchorCoupling coupling{i} x) origin{i} i := by
  exact physical_anchor_nonneg Finset.univ (rayDegree rays{i}) (rayO rays{i} originDen{i})
    (rayV rays{i} featureDen{i}) F{i} b{i} v{i} countM{i} x hx ({countProof})

def TriangleSign : Prop := ∀ a b t : ℝ,
  -1 ≤ a → a ≤ {s} → -1 ≤ b → b ≤ {s} → -1 ≤ t → t ≤ {s} →
  0 ≤ 1+2*a*b*t-a^2-b^2-t^2 →
  kernel{i} a b t+kernel{i} a t b+kernel{i} b t a ≤ 3*(epsilon{i}:ℝ)

theorem raw_upper_of_triangle (hT : TriangleSign) {{n : ℕ}} {condition}
    (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ {s}) :
    (∑ i, ∑ j, V7.sphericalScalar ⟪x i,x j⟫) ≤
      (n:ℝ)*rawB+(eta{i}:ℝ)*n*(n-1)+(epsilon{i}:ℝ)*n*(n-1)*(n-2) := by
  have h := raw_spherical_upper g{i} coupling{i} kernel{i} origin{i} ({s}) epsilon{i} eta{i}
    x hx hxs rawPair{i}_le hT (floor hN x hx)
  rw [rawB_eq] at h
  simpa only [scalar_eq] using h

theorem repaired_upper_of_triangle (hT : TriangleSign) {{n : ℕ}} {condition}
    (x : Fin n → E4) (hx : ∀ i, ‖x i‖=1)
    (hxs : ∀ i j, i ≠ j → ⟪x i,x j⟫ ≤ {s}) :
    (∑ i, ∑ j, V7.sphericalScalar ⟪x i,x j⟫) ≤ (n:ℝ)*repairedB := by
  have h := repaired_spherical_upper g{i} coupling{i} SphericalConcrete.C26.T kernel{i}
    origin{i} ({s}) epsilon{i} eta{i} SphericalConcrete.C26.D {n} x hx hxs
    (by norm_num [epsilon{i}]) (by norm_num [epsilon{i},eta{i},SphericalConcrete.C26.D])
    ({hM}) SphericalConcrete.C26.repair_diag
    (fun t hlo hhi => SphericalConcrete.C26.repair_sign t hlo (by linarith)) repair_psd
    rawPair{i}_le hT (floor hN x hx)
  rw [rawB_eq,repairedB_eq] at h
  simpa only [scalar_eq] using h

#print axioms raw_upper_of_triangle
#print axioms repaired_upper_of_triangle
end D4Bound.SphericalSurplusBounds.B{i}
'''
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
 for i in range(3):
  p=HERE.parent/f'D4Bound/SphericalSurplusBounds{i}.lean';s=generate(i)
  if a.check:assert p.read_text()==s
  else:p.write_text(s)
 print('PASS: surplus bounds source regeneration' if a.check else 'Generated three surplus bound modules')
