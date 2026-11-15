"""Generate literal spherical arithmetic proofs; Lean checks every identity."""
from pathlib import Path
from fractions import Fraction as Q
import json, math, argparse
P=Path(__file__).resolve().parents[2]
S=P/'verify/stage1_v7/record/current/base/new_work/spherical_sdp'
L=P/'lean/D4Bound'
args=argparse.ArgumentParser();args.add_argument('--check',action='store_true');args=args.parse_args()
def write(name,s):
 p=L/(name+'.lean')
 if args.check: assert p.read_text()==s,name
 elif not p.exists() or p.read_text()!=s:p.write_text(s)
def rat(q):
 q=Q(q);return f'({q.numerator}/{q.denominator})'
def horner(cs):
 s='0'
 for c in reversed(cs):s=f'({c} + t * {s})'
 return s
for n in range(21,25):
 prev='Basic' if n==21 else 'U'+str(n-1)
 s=f'import D4Bound.SphericalConcrete{prev}\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 30000\nset_option Elab.async false\nnamespace D4Bound.SphericalConcrete\nopen AnnularCertificate\n'
 cs=[0]*(n+1)
 for j in range(n//2+1):cs[n-2*j]=(-1)**j*math.comb(n-j,j)*2**(n-2*j)
 s+=f'''\nlemma U{n} (t : ℝ) : (Polynomial.Chebyshev.U ℝ ({n} : ℤ)).eval t = {horner(cs)} := by
  rw [show ({n} : ℤ) = {n-2} + 2 by norm_num, Polynomial.Chebyshev.U_add_two]
  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  rw [U{n-1}, U{n-2}]
  ring
'''
 s+='\nend D4Bound.SphericalConcrete\n';write('SphericalConcreteU'+str(n),s)
write('SphericalConcretePolynomials','import D4Bound.SphericalConcreteU24\n')
for n,fn in [(24,'s05075_taper12_exact.json'),(25,'s0515_count25_exact.json'),(26,'s0525_count26_exact.json')]:
 d=json.loads((S/fn).read_text());rc=list(map(Q,d['uniform_repair']['gegenbauer_coefficients']));a=rc[0];N=len(rc)-1
 sc=[Q(v,d['scalar_scale']*(i+1)) for i,v in enumerate(d['scalar'])][1:]
 rcw=[v/(a*(i+1)) for i,v in enumerate(rc)][1:]
 D=sum(rc)/a-1;originNum=sum(r[0]**2 for r in d['blocks'][0]);origin=Q(originNum,d['feature_scale']**2);g1=Q(sum(d['scalar']),d['scalar_scale']);sval=Q(d['s']);ep=Q(d['uniform_repair']['scale'])
 us=', '.join('U'+str(i) for i in range(1,25))
 s=f'''-- Generated from {fn}; every arithmetic identity is kernel checked.
import D4Bound.SphericalConcretePolynomials
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign AnnularCertificate
namespace C{n}
noncomputable def g (t : ℝ) : ℝ := evalZ scalarPower{n} t / scalarPowerDen{n}
noncomputable def scalarWeights : Fin 24 → ℝ := ![{', '.join(map(rat,sc))}]
noncomputable def scalarRest (t : ℝ) : ℝ := ∑ i : Fin 24, scalarWeights i * (Polynomial.Chebyshev.U ℝ (i.val+1 : ℤ)).eval t
noncomputable def repairWeights : Fin {N} → ℝ := ![{', '.join(map(rat,rcw))}]
noncomputable def T (t : ℝ) : ℝ := ∑ i : Fin {N}, repairWeights i * (Polynomial.Chebyshev.U ℝ (i.val+1 : ℤ)).eval t
noncomputable def D : ℝ := {rat(D)}
theorem scalar_nonneg (i : Fin 24) : 0 ≤ scalarWeights i := by
  fin_cases i <;> norm_num [scalarWeights]
theorem repair_nonneg (i : Fin {N}) : 0 ≤ repairWeights i := by
  fin_cases i <;> norm_num [repairWeights]
theorem scalar_identity (t : ℝ) : g t - 1 = scalarRest t := by
  norm_num [g, scalarRest, scalarWeights, Fin.sum_univ_succ, {us}, scalarPower{n}, scalarPowerDen{n}, evalZ]
  <;> ring
theorem repair_identity (t : ℝ) : T t = evalZ repair{n} t / repair{n}Den / {rat(a)} - 1 := by
  norm_num [T, repairWeights, Fin.sum_univ_succ, {us}, repair{n}, repair{n}Den, evalZ]
  <;> ring
theorem repair_sign (t : ℝ) (hlo : -1 ≤ t) (hhi : t ≤ {rat(sval)}) : T t ≤ -1 := by
  rw [repair_identity]
  have h := repair{n}_nonpos t hlo hhi
  have hd : (0:ℝ) < repair{n}Den := by norm_num [repair{n}Den]
  have hp := div_nonpos_of_nonpos_of_nonneg h hd.le
  have hq := div_nonpos_of_nonpos_of_nonneg hp (show (0:ℝ) ≤ {rat(a)} by norm_num)
  linarith
theorem repair_diag : T 1 = D := by
  norm_num [T, repairWeights, D, Fin.sum_univ_succ, Polynomial.Chebyshev.U_eval_one]
theorem scalar_diag : g 1 = {rat(g1)} := by
  norm_num [g, scalarPower{n}, scalarPowerDen{n}, evalZ]
theorem origin_check : originNumerator rays{n} = {originNum} := by decide +kernel
theorem origin_value : SphereCertificate.origin Finset.univ (rayDegree rays{n}) (rayO rays{n} originDen{n}) = {rat(origin)} := by
  rw [origin_eq, origin_check]
  norm_num [originDen{n}]
theorem decrease : (epsilon{n}:ℝ)*D + 0 < 1 := by norm_num [epsilon{n}, D]
theorem objective : g 1 + SphereCertificate.origin Finset.univ (rayDegree rays{n}) (rayO rays{n} originDen{n}) - ((epsilon{n}:ℝ)*D+0) < ({n}+1:ℕ)*(1-((epsilon{n}:ℝ)*D+0)) := by
  rw [scalar_diag, origin_value]
  norm_num [epsilon{n}, D]
end C{n}
end D4Bound.SphericalConcrete
'''
 header=s[:s.index('noncomputable def g')]
 close=f'end C{n}\nend D4Bound.SphericalConcrete\n'
 data=s[:s.index('theorem scalar_identity')]+close
 scalar=header.replace('SphericalConcretePolynomials',f'SphericalConcreteData{n}')+s[s.index('theorem scalar_identity'):s.index('theorem repair_identity')]+s[s.index('theorem scalar_diag'):s.index('theorem origin_check')]+close
 repair=header.replace('SphericalConcretePolynomials',f'SphericalConcreteData{n}')+s[s.index('theorem repair_identity'):s.index('theorem scalar_diag')]+close
 arithmetic=header.replace('import D4Bound.SphericalConcretePolynomials',f'import D4Bound.SphericalConcreteScalar{n}\nimport D4Bound.SphericalConcreteRepair{n}')+s[s.index('theorem origin_check'):]
 write('SphericalConcreteData'+str(n),data)
 write('SphericalConcreteScalar'+str(n),scalar)
 write('SphericalConcreteRepair'+str(n),repair)
 write('SphericalConcreteArithmetic'+str(n),arithmetic)
for n,sval in [(24,Q(203,400)),(25,Q(103,200)),(26,Q(21,40))]:
 N=20 if n==24 else 24
 s=f'''import D4Bound.SphericalConcreteArithmetic{n}
import D4Bound.SphericalCertCompose
import D4Bound.SphericalSignTriangle{n}
import D4Bound.SphericalSignNative{n}
set_option maxHeartbeats 0
set_option Elab.async false
open Finset
namespace D4Bound.SphericalConcrete
open SphericalSign SphereCertificate
namespace C{n}
theorem scalar_psd : SpherePSD (fun t => g t-1) := by
  have h := harmonic_PSD Finset.univ (fun i : Fin 24 => i.val+1) scalarWeights (fun i _ => scalar_nonneg i)
  simpa only [scalar_identity, scalarRest, Nat.cast_add, Nat.cast_one] using h
theorem repair_psd : SpherePSD T := by
  exact harmonic_PSD Finset.univ (fun i : Fin {N} => i.val+1) repairWeights (fun i _ => repair_nonneg i)
theorem code_bound (hc : Bernstein.OnCube Bernstein.upper{n} Bernstein.gramUpper{n}) :
    SphericalCodeBound {rat(sval)} {n} := by
  apply code_bound_from_rays Finset.univ (rayDegree rays{n}) (rayO rays{n} originDen{n}) (rayV rays{n} featureDen{n}) g T {rat(sval)} (epsilon{n}:ℝ) 0 D {n}
  · exact scalar_psd
  · exact repair_psd
  · norm_num [epsilon{n}]
  · exact repair_diag
  · exact repair_sign
  · exact rawPair{n}_nonpos
  · exact Bernstein.rawTriangle{n}_of_cube hc
  · exact decrease
  · exact objective

/-- The whole-tree check (`SphericalSignNative`, run by `native_decide`) discharges the OnCube premise. -/
theorem code_bound_unconditional : SphericalCodeBound {rat(sval)} {n} :=
  code_bound Bernstein.Native.onCube{n}
#print axioms code_bound_unconditional

#print axioms code_bound
end C{n}
end D4Bound.SphericalConcrete
'''
 write('SphericalConcrete'+str(n),s)

print('PASS spherical concrete source generation')
