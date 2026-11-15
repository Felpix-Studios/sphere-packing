"""Generate exact Lean proof that A(3,223/735)<=8.

Only the rational certificate is input. The producer is untrusted: Lean checks
the Legendre expansion, full interval sign cover, coefficient signs and bound.
"""
import argparse,json,math
from fractions import Fraction as Q
from pathlib import Path
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parents[1]/'data/projected_eight.json'
TARGET=HERE.parent/'D4Bound/ProjectedEightCert.lean'
def add(p,q):
 r=[Q(0)]*max(len(p),len(q))
 for i,c in enumerate(p):r[i]+=c
 for i,c in enumerate(q):r[i]+=c
 return r
def rat(q):return f'({q.numerator}/{q.denominator})'
def horner(p,t):
 s='0'
 for c in reversed(p):s=f'({rat(c)} + {t} * {s})'
 return s
def generate():
 data=json.loads(SOURCE.read_text());assert data['cutoff']=='223/735'
 a=list(map(Q,data['coefficients']));N=len(a)-1
 assert a[0]>0 and all(c>=0 for c in a) and sum(a)<9*a[0]
 U=[[Q(1)],[Q(0),Q(1)]]
 for k in range(2,N+1):
  U.append(add([0]+[Q(2*k-1,k)*c for c in U[-1]],[-Q(k-1,k)*c for c in U[-2]]))
 p=[Q(0)]
 for k,c in enumerate(a):p=add(p,[c*v for v in U[k]])
 r=[-sum((c*math.comb(j,k)*(-1)**(j-k)*Q(958,735)**k for j,c in enumerate(p) if j>=k),Q()) for k in range(N+1)]
 D=math.lcm(*(c.denominator for c in r));P=[int(c*D) for c in r]
 def leaf(A,k):
  d=2**k
  cs=[sum(P[j]*math.comb(j,i)*A**(j-i)*d**(N-j) for j in range(i,N+1)) for i in range(N+1)]
  v=0
  for c in reversed(cs):v=c+min(v,0)
  return v>0
 stack=[(0,0)];L=[]
 while stack:
  A,k=stack.pop();assert k<50 and len(L)<10000
  if leaf(A,k):L.append((A,k,1))
  else:stack.extend([(2*A+1,k+1),(2*A,k+1)])
 print(f'Exact certificate: {len(L)} leaves, depth {max(k for _,k,_ in L)}, objective {float(sum(a)/a[0]):.12f}')
 out=['''import D4Bound.SphericalCertS2Basic
import D4Bound.ScalarCheck

/-! Exact Legendre certificate for the graph's projected degree bound.
The polynomial has degree27. Its sign is checked on the entire closed interval
[-1,223/735], including its endpoint; no sampled inequalities are used. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset
open scoped RealInnerProductSpace
namespace D4Bound
namespace ProjectedEightCertificate
''']
 out += [f'def numerators : List ℤ := {P}\n',f'def denominator : ℤ := {D}\n',f'def leaves : List (ℕ × ℕ × ℕ) := {L}\n']
 out += ['theorem sign_check : chainOK numerators 0 0 leaves 1 0 = true := by decide +kernel\n']
 out += ['theorem endpoint_check : 0 < evalZ numerators 1 := by norm_num [numerators, evalZ]\n']
 nonzero=[k for k in range(1,N+1) if a[k]]
 n=len(nonzero)
 out += [f'noncomputable def coefficients : Fin {n} → ℝ := ![{", ".join(rat(a[k]) for k in nonzero)}]\n']
 out += [f'def degrees : Fin {n} → ℕ := ![{", ".join(map(str,nonzero))}]\n']
 out += [f'noncomputable def rest (t : ℝ) : ℝ := ∑ i : Fin {n}, coefficients i * Schoenberg2.legendre (degrees i) t\n']
 for k,u in enumerate(U):
  out += [f'lemma P{k} (t : ℝ) : Schoenberg2.legendre {k} t = {horner(u,"t")} := by\n']
  if k<2:out += ['  simp <;> ring\n']
  else:
   out += [f'  rw [Schoenberg2.legendre_recurrence {k-2}]\n',f'  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]\n',f'  rw [P{k-1}, P{k-2}]\n  ring\n']
 out += [f'''theorem coefficients_nonneg (i : Fin {n}) : 0 ≤ coefficients i := by
  fin_cases i <;> norm_num [coefficients]

theorem rest_energy : Sphere2EnergyNonneg rest := by
  exact sphere2Energy_sum Finset.univ coefficients degrees
    (fun i _ => coefficients_nonneg i)
''']
 out += [f'''theorem polynomial_identity (u : ℝ) :
    {rat(a[0])} + rest ((958*u-735)/735) = -evalZ numerators u / denominator := by
  norm_num [rest, coefficients, degrees, Fin.sum_univ_succ, {', '.join('P'+str(k) for k in nonzero)}, numerators, denominator, evalZ]
  <;> ring

theorem sign (t : ℝ) (ht0 : -1 ≤ t) (ht1 : t ≤ 223/735) :
    {rat(a[0])} + rest t ≤ 0 := by
  let u : ℝ := (735*t+735)/958
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hp : 0 < evalZ numerators u := by
    rcases lt_or_eq_of_le hu1 with hlt | heq
    · exact chainOK_sound numerators leaves 0 0 1 0 sign_check u (by simpa using hu0) (by simpa using hlt)
    · simpa [heq] using endpoint_check
  have he := polynomial_identity u
  have hu : (958*u-735)/735 = t := by dsimp [u]; ring
  rw [hu] at he
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num [denominator])

theorem diagonal : {rat(a[0])} + rest 1 = {rat(sum(a))} := by
  norm_num [rest, coefficients, degrees, Fin.sum_univ_succ]

end ProjectedEightCertificate

/-- A sufficient replacement for the cited nine-point theorem at the precise
projected cutoff required by the broad antipodal graph. -/
theorem projected_eight_proved
    (C : Finset (EuclideanSpace ℝ (Fin 3))) (hC : ∀ u ∈ C, ‖u‖ = 1)
    (hsep : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ⟪u,v⟫ ≤ 223/735) : C.card ≤ 8 := by
  apply sphericalCodeBound3_of_energy (223/735) {rat(a[0])} {rat(sum(a))} 8
    ProjectedEightCertificate.rest (by norm_num) (by norm_num)
    ProjectedEightCertificate.rest_energy ProjectedEightCertificate.diagonal
    ProjectedEightCertificate.sign C hC hsep

#print axioms projected_eight_proved
end D4Bound
''']
 return '\n'.join(out)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();s=generate()
 if a.check:assert TARGET.read_text()==s;print('PASS: projected8 exact source regeneration')
 else:TARGET.write_text(s);print(TARGET)
