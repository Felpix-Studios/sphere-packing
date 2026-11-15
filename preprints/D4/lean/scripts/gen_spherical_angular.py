"""Generate checked polynomial identities for all angular degrees used by near-code inputs."""
from pathlib import Path
from fractions import Fraction
from math import comb
import argparse
HERE=Path(__file__).resolve().parent
TARGET=HERE.parent/'D4Bound/SphericalCertAngular.lean'
def generate():
 out=['''import D4Bound.SphericalCertLegendre
/-! Explicit homogeneous Legendre polynomials used by the spherical JSON verifier.
Each equality is proved from the normalized three-term recurrence. -/
namespace D4Bound.Schoenberg2
''']
 for n in range(13):
  terms=[]
  for j in range(n//2+1):
   c=Fraction((-1)**j*comb(n,j)*comb(2*n-2*j,n),2**n)
   terms.append(f'({c.numerator}/{c.denominator})*u^{n-2*j}*v^{j}')
  out.append(f'lemma solid_poly_{n} (u v : ℝ) : solidLegendre u v {n} = '+ ' + '.join(terms)+' := by\n')
  if n<2:out.append('  simp [solidLegendre]\n')
  else:out.append(f'  rw [solidLegendre, solid_poly_{n-1}, solid_poly_{n-2}]\n  norm_num\n  <;> ring\n')
 out.append('\nend D4Bound.Schoenberg2\n');return ''.join(out)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();s=generate()
 if a.check:assert TARGET.read_text()==s;print('PASS: homogeneous angular source regeneration')
 else:TARGET.write_text(s);print(TARGET)
