"""Generate exact Lean data/proof for the published degree-20 annular certificate.
The generator is not trusted: all arithmetic and interval coverage are rechecked in Lean.
"""
import argparse,json,math
from fractions import Fraction as Q
from pathlib import Path
HERE=Path(__file__).resolve().parent
PKG=HERE.parents[1]
SOURCE=PKG/'verify/stage4_graph_slack/src/annular_count_151_certificate.json'
TARGET=HERE.parent/'D4Bound/AnnularCert.lean'

def add(p,q):
 r=[Q(0)]*max(len(p),len(q))
 for i,c in enumerate(p):r[i]+=c
 for i,c in enumerate(q):r[i]+=c
 return r

def horner(p,t):
 s='0'
 for c in reversed(p):s=f'({int(c)} + {t} * {s})'
 return s

def rat(q):return f'({q.numerator} / {q.denominator})'

def generate():
 a=list(map(Q,json.loads(SOURCE.read_text())['harmonic_coefficients']))
 assert len(a)==21 and all(c>=0 for c in a) and a[0]>0
 U=[[1],[0,2]]
 for k in range(2,21):U.append(add([0]+[2*c for c in U[-1]],[-c for c in U[-2]]))
 p=[Q(0)]
 for k,c in enumerate(a):p=add(p,[c*Q(v,k+1) for v in U[k]])
 r=[-sum((c*math.comb(j,k)*(-1)**(j-k)*Q(90,49)**k for j,c in enumerate(p) if j>=k),Q()) for k in range(21)]
 D=math.lcm(*(c.denominator for c in r));P=[int(c*D) for c in r]
 def leaf(A,k):
  d=2**k
  cs=[sum(P[j]*math.comb(j,i)*A**(j-i)*d**(20-j) for j in range(i,21)) for i in range(21)]
  v=0
  for c in reversed(cs):v=c+min(v,0)
  return v>0
 stack=[(0,0)];L=[]
 while stack:
  A,k=stack.pop();assert k<50 and len(L)<10000
  if leaf(A,k):L.append((A,k,1))
  else:stack.extend([(2*A+1,k+1),(2*A,k+1)])
 out=['''import D4Bound.SphericalCertBasic
import D4Bound.ScalarCheck

/-! Exact degree-20 annular Delsarte certificate, generated from the publication JSON.
Every coefficient identity, dyadic interval, and final objective is kernel checked. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset
open scoped RealInnerProductSpace
namespace D4Bound
namespace AnnularCertificate
''']
 out += [f'def numerators : List ℤ := {P}\n',f'def denominator : ℤ := {D}\n',f'def leaves : List (ℕ × ℕ × ℕ) := {L}\n'.replace('(', '(')]
 # Python list of tuples already has correct Lean notation.
 out += ['theorem sign_check : chainOK numerators 0 0 leaves 1 0 = true := by decide +kernel\n']
 out += ['theorem endpoint_check : 0 < evalZ numerators 1 := by norm_num [numerators, evalZ]\n']
 out += [f'noncomputable def coefficients : Fin 20 → ℝ := ![{", ".join(rat(a[k]/(k+1)) for k in range(1,21))}]\n']
 out += ['noncomputable def rest (t : ℝ) : ℝ := ∑ i : Fin 20, coefficients i * (Polynomial.Chebyshev.U ℝ (i.val + 1 : ℤ)).eval t\n']
 for k,u in enumerate(U):
  out += [f'lemma U{k} (t : ℝ) : (Polynomial.Chebyshev.U ℝ ({k} : ℤ)).eval t = {horner(u,"t")} := by\n']
  if k<2:out += ['  simp [Polynomial.Chebyshev.U_one] <;> ring\n']
  else:
   out += [f'  rw [show ({k} : ℤ) = {k-2} + 2 by norm_num, Polynomial.Chebyshev.U_add_two]\n',f'  norm_num only [Int.reduceAdd, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]\n',f'  rw [U{k-1}, U{k-2}]\n  ring\n']
 out += ['''theorem coefficients_nonneg (i : Fin 20) : 0 ≤ coefficients i := by
  fin_cases i <;> norm_num [coefficients]

 theorem rest_energy : SphereEnergyNonneg rest := by
  exact sphereEnergy_sum Finset.univ coefficients (fun i : Fin 20 => i.val + 1)
    (fun i _ => coefficients_nonneg i)
''']
 out += [f'''theorem polynomial_identity (u : ℝ) :
    {rat(a[0])} + rest ((90*u-49)/49) = -evalZ numerators u / denominator := by
  norm_num [rest, coefficients, Fin.sum_univ_succ, {', '.join('U'+str(k) for k in range(1,21))}, numerators, denominator, evalZ]
  <;> ring
''']
 out += [f'''theorem sign (t : ℝ) (ht0 : -1 ≤ t) (ht1 : t ≤ 41/49) :
    {rat(a[0])} + rest t ≤ 0 := by
  let u : ℝ := (49*t+49)/90
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hp : 0 < evalZ numerators u := by
    rcases lt_or_eq_of_le hu1 with hlt | heq
    · exact chainOK_sound numerators leaves 0 0 1 0 sign_check u (by simpa using hu0) (by simpa using hlt)
    · simpa [heq] using endpoint_check
  have he := polynomial_identity u
  have hu : (90*u-49)/49 = t := by dsimp [u]; ring
  rw [hu] at he
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num [denominator])

 theorem diagonal : {rat(a[0])} + rest 1 = {rat(sum(a))} := by
  norm_num [rest, coefficients, Fin.sum_univ_succ, Polynomial.Chebyshev.U_eval_one]

end AnnularCertificate

/-- The published annular code count, proved without a certificate hypothesis. -/
theorem annular_151_proved : SphericalCodeBound (41/49) 151 := by
  apply sphericalCodeBound_of_energy (41/49) {rat(a[0])} {rat(sum(a))} 151 AnnularCertificate.rest
  · norm_num
  · norm_num
  · exact AnnularCertificate.rest_energy
  · exact AnnularCertificate.diagonal
  · exact AnnularCertificate.sign

#print axioms annular_151_proved
end D4Bound
''']
 return '\n'.join(out)

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args();text=generate()
 if args.check:
  assert TARGET.read_text()==text,'generated AnnularCert.lean differs'
  print('PASS: exact annular source regeneration')
 else:TARGET.write_text(text);print(TARGET)
