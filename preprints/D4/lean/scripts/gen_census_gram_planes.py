"""Export twelve exact radial supporting-plane proofs with closed interval coverage."""
from pathlib import Path
import json,math,argparse
from fractions import Fraction as Q
from census_gram_inputs import validate_planes
ROOT=Path(__file__).resolve().parents[1]; P=ROOT.parent
args_parser=argparse.ArgumentParser()
args_parser.add_argument('--check',action='store_true')
args=args_parser.parse_args()
def emit(path,text):
 if args.check:
  if path.read_text()!=text:raise SystemExit(f'Generated source mismatch: {path}')
 else:path.write_text(text)
rows=json.loads((P/'verify/stage2_origin/reference/RADIAL_PLANES.json').read_text())
validate_planes(rows)
def rat(q,typ='ℝ'):
 q=Q(q);return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator} : {typ})'
def tree(v):
 if min(v)>=0:return '(.leaf)'
 levels=[v]
 while len(levels[-1])>1:levels.append([(a+b)/2 for a,b in zip(levels[-1],levels[-1][1:])])
 l=[a[0] for a in levels];r=[a[-1] for a in levels[::-1]]
 return f'(.split {tree(l)} {tree(r)})'
for j,row in enumerate(rows):
 s='''import D4Bound.V7CensusGramRadial
import D4Bound.V7CensusGramPlaneData
namespace D4Bound.V7.CensusGram
open Bernstein
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
 for k,p in enumerate(row['pieces']):
  a,b=map(Q,p['physical_interval']);lo=Q(p['certified_lower_bound'])
  coeffs=[Q(x)-lo for x in p['exact_restricted_Bernstein_coefficients']];D=math.lcm(*(q.denominator for q in coeffs));v=[int(x*D) for x in coeffs]
  s+=f'def plane{j}piece{k} : Seven ℤ := ⟨'+','.join(map(str,v))+'⟩\n'
  s+=f'def plane{j}tree{k} : Tree := {tree(coeffs)}\n'
  s+=f'theorem plane{j}check{k} : check plane{j}piece{k} plane{j}tree{k} = true := by decide +kernel\n'
  s+=f'''theorem plane{j}piece_bound{k} (r : ℝ) (ha : {rat(a)} ≤ r) (hb : r ≤ {rat(b)}) :
    {rat(lo)} ≤ pieceValue planeLinear{j} {k} r := by
  have h := check_sound plane{j}tree{k} plane{j}piece{k} plane{j}check{k}
    (x := (r-{rat(a)})/{rat(b-a)})
    (by apply div_nonneg <;> linarith)
    (by apply (div_le_one (by norm_num : (0:ℝ) < {rat(b-a)})).mpr; linarith)
  have he : eval (plane{j}piece{k}.map Int.cast) ((r-{rat(a)})/{rat(b-a)}) =
      {D} * (pieceValue planeLinear{j} {k} r - {rat(lo)}) := by
    norm_num [eval, Seven.map, plane{j}piece{k}, pieceValue, planeLinear{j}, basisValue,
      basisIntervals, List.range_succ, Nat.choose]
    ring
  rw [he] at h
  nlinarith

'''
 s+=f'''theorem plane{j}_radial (r : ℝ) (hr1 : 1 ≤ r) (hrR : r ≤ 7/4) :
    ((List.range 5).map fun i => (planeCounts{j}.getD i 0 : ℝ)*
      indicator (breaks.getD (i+1) 0) r).sum ≤ radialValue planeLinear{j} r := by
  rw [radialValue_eq_pieceValue, radialPiece_on_support hrR]
  split_ifs with h0 h1 h2 h3 h4 h5
'''
 for k,p in enumerate(row['pieces']):
  a,b=map(Q,p['physical_interval']);lo=Q(p['certified_lower_bound'])
  s+=f'  · have hp := plane{j}piece_bound{k} r (by linarith) (by linarith)\n'
  for l in range(k+1,5):
   boundary=Q(row['pieces'][l]['physical_interval'][1])
   s+=f'    have h{l} : r ≤ {rat(boundary)} := by linarith\n'
  names=', '.join(['h'+str(l) for l in range(max(min(k+1,6),5))])
  s+=f'    norm_num [planeCounts{j}, List.range_succ, breaks, indicator, {names}] at hp ⊢\n'
  s+='    exact hp\n'
 s+='end\nend D4Bound.V7.CensusGram\n'
 emit(ROOT/f'D4Bound/V7CensusGramPlane{j}.lean',s)
print(('PASS: checked' if args.check else 'Generated')+' 12 radial plane proof modules')
