"""Generate the small, kernel-checked rational surplus table comparison."""
from pathlib import Path
from fractions import Fraction as Q
import json,argparse,re,math
HERE=Path(__file__).resolve().parent;PKG=HERE.parents[1]
TARGET=HERE.parent/'D4Bound/SphericalSurplusTable.lean'
def rat(q):return f'({q.numerator}/{q.denominator})'
def generate():
 records=[json.loads((PKG/f'verify/stage2_origin/reference/ANGULAR_{i}.json').read_text()) for i in range(3)]
 a=records[0]['accepted_combination']; W=Q(a['positive_normalization']);B=Q(a['weighted_accepted_B'])
 out=['''import D4Bound.CensusEnvelope
/-! The exact 27 by 5 table of applicable spherical surplus maxima.
This is rational arithmetic only; the analytic bounds are proved separately. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace D4Bound.SphericalSurplusTable
open CensusArithmetic
''']
 out += [f'def W : ℚ := {rat(W)}\n',f'def B : ℚ := {rat(B)}\n']
 for i,r in enumerate(records):
  rep=r['normalized_B'] if i==1 else r['B']
  for name,v in [('raw',r['raw_B']),('repaired',rep),('epsilon',r['repair']['scale']),('eta',r['repair']['pair_shift'])]:out += [f'def {name}{i} : ℚ := {rat(Q(v))}\n']
  out += [f'def credit{i} (n : ℕ) : ℚ := max (n*(B-W*repaired{i})) (n*B-W*(n*raw{i}+eta{i}*n*(n-1)+epsilon{i}*n*(n-1)*(n-2)))\n']
 D=int(re.search(r'def denominator : ℤ := (\d+)',(HERE.parent/'D4Bound/CensusData.lean').read_text()).group(1))
 E=D
 for i,r in enumerate(records):
  rep=Q(r['normalized_B'] if i==1 else r['B'])
  for c in [B-W*rep,B-W*Q(r['raw_B']),W*Q(r['repair']['pair_shift']),W*Q(r['repair']['scale'])]: E=math.lcm(E,c.denominator)
 factor=E//D
 out += [f'def scaleFactor : ℤ := {factor}\n',f'def scaleDen : ℤ := {E}\n']
 for i,r in enumerate(records):
  rep=Q(r['normalized_B'] if i==1 else r['B'])
  cs=[B-W*rep,B-W*Q(r['raw_B']),W*Q(r['repair']['pair_shift']),W*Q(r['repair']['scale'])]
  C=[int(c*E) for c in cs];assert all(c*E==z for c,z in zip(cs,C))
  out += [f'def scaledCredit{i} (n : ℕ) : ℤ := max (n*{C[0]}) (n*{C[1]}-{C[2]}*n*(n-1)-{C[3]}*n*(n-1)*(n-2))\n']
  out += [f'''theorem credit_scaled{i} (n : ℕ) :
    (scaleDen:ℝ)*(credit{i} n:ℝ) = (scaledCredit{i} n:ℝ) := by
  unfold credit{i} scaledCredit{i}
  push_cast
  rw [mul_max_of_nonneg _ _ (by norm_num [scaleDen] : (0:ℝ)≤scaleDen)]
  congr 1 <;> norm_num [scaleDen,B,W,repaired{i},raw{i},epsilon{i},eta{i}] <;> ring
''']
 out += ['''def available (n j : ℕ) : ℚ :=
  max 0 (max (credit1 n) (max (if n=24 ∧ j≤1 then credit0 n else 0)
    (if n=25 ∧ j≤4 then credit2 n else 0)))

def scaledAvailable (n j : ℕ) : ℤ :=
  max 0 (max (scaledCredit1 n) (max (if n=24 ∧ j≤1 then scaledCredit0 n else 0)
    (if n=25 ∧ j≤4 then scaledCredit2 n else 0)))

theorem available_scaled (n j : ℕ) :
    (scaleDen:ℝ)*(available n j:ℝ) = (scaledAvailable n j:ℝ) := by
  unfold available scaledAvailable
  push_cast
  split_ifs <;>
    simp only [Rat.cast_zero,Int.cast_zero,mul_max_of_nonneg _ _ (by norm_num [scaleDen] : (0:ℝ)≤scaleDen),
      mul_zero,credit_scaled0,credit_scaled1,credit_scaled2]

theorem table_checked : ∀ n : Fin 27, ∀ j : Fin 5,
    surplusNumerators[5*n.val+j.val]!*scaleFactor ≤ scaledAvailable n.val (j.val+1) := by
  decide +kernel

lemma first_pos (v : Counts) : 1 ≤ first v := by
  unfold first
  split_ifs <;> omega
lemma first_le_five (v : Counts) : first v ≤ 5 := by
  unfold first
  split_ifs <;> omega

theorem surplus_part_le (v : Counts) (h : v.n4≤26) :
    surplusPart v ≤ (available v.n4 (first v) : ℝ) := by
  have hj := first_pos v
  have hj' := first_le_five v
  have he := table_checked ⟨v.n4,by omega⟩ ⟨first v-1,by omega⟩
  have hjv : first v-1+1=first v := by omega
  have hindex : 5*v.n4+(first v-1)=5*v.n4+first v-1 := by omega
  simp only [hjv,hindex] at he
  have heR : (surplusNumerators[5*v.n4+first v-1]!:ℝ)*scaleFactor ≤ (scaledAvailable v.n4 (first v):ℝ) := by exact_mod_cast he
  have hE : (0:ℝ)<scaleDen := by norm_num [scaleDen]
  apply (mul_le_mul_iff_right₀ hE).mp
  rw [available_scaled]
  have hidentity : (scaleDen:ℝ)*surplusPart v = (surplusNumerators[5*v.n4+first v-1]!:ℝ)*scaleFactor := by
    unfold surplusPart
    norm_num [scaleDen,scaleFactor,denominator]
    ring
  rw [hidentity]
  exact heR

theorem available_le (n j : ℕ) (E : ℝ) (hzero : 0≤E)
    (h1 : (credit1 n:ℝ)≤E)
    (h0 : n=24 → j≤1 → (credit0 n:ℝ)≤E)
    (h2 : n=25 → j≤4 → (credit2 n:ℝ)≤E) : (available n j:ℝ)≤E := by
  unfold available
  push_cast
  apply max_le hzero
  apply max_le h1
  apply max_le
  · split_ifs with h
    · exact h0 h.1 h.2
    · simpa using hzero
  · split_ifs with h
    · exact h2 h.1 h.2
    · simpa using hzero

#print axioms surplus_part_le
end D4Bound.SphericalSurplusTable
''']
 return '\n'.join(out)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();s=generate()
 if a.check:assert TARGET.read_text()==s;print('PASS: spherical surplus table regeneration')
 else:TARGET.write_text(s);print(TARGET)
