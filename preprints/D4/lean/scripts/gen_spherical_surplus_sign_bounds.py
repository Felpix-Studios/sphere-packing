"""Exact raw and repaired objective constants linked to concrete reduced rays."""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import json

PKG = Path(__file__).resolve().parents[2]
SOURCE = PKG / 'verify/stage2_origin/source'
OUT = PKG / 'lean/D4Bound'
ap = argparse.ArgumentParser()
ap.add_argument('--check', action='store_true')
args = ap.parse_args()
registry = json.loads((SOURCE / 'target625/origin_completion/FINAL_ORIGIN_REGISTRY.json').read_text())
for n, entry in enumerate(registry['common_g_certificates']):
    data = json.loads((SOURCE / entry['certificate']).read_text())
    reference = json.loads((PKG / f'verify/stage2_origin/reference/ANGULAR_{n}.json').read_text())
    origin_sum = sum(r[0]**2 for r in data['blocks'][0])
    count = data.get('fixed_count') or 26
    eps = Q(reference['repair']['scale'])
    eta = Q(reference['repair']['pair_shift'])
    diag = Q(reference['repair']['diagonal'])
    raw = Q(reference['raw_B'])
    bound = Q(reference['B'] if 'B' in reference else reference['normalized_B'])
    assert raw + (count - 1) * (eta + eps * diag) == bound
    lines = ['-- Exact constants are tied to rays and scalar polynomial below.',
        f'import D4Bound.SphericalSurplusSignData{n}',
        'import D4Bound.SphericalConcreteBasic', 'set_option maxHeartbeats 0',
        'set_option maxRecDepth 20000', 'set_option Elab.async false',
        'namespace D4Bound.SphericalSurplusSign', 'open SphericalSign SphericalConcrete',
        f'def rawBound{n} : ℚ := {raw}', f'def repairedBound{n} : ℚ := {bound}',
        f'def maxCount{n} : ℕ := {count}', f'def repairDiagonal{n} : ℚ := {diag}',
        f'''theorem originNumerator{n}_exact : originNumerator rays{n} = {origin_sum} := by
  decide +kernel''',
        f'''theorem rawBound{n}_correct : g{n} 1 + origin{n} = (rawBound{n}:ℝ) := by
  unfold origin{n}
  rw [origin_eq, originNumerator{n}_exact]
  norm_num [g{n},scalarPower{n},scalarPowerDen{n},evalZ,originDen{n},countM{n},
    v{n},vNum{n},b{n},bNum{n},rawBound{n}]''',
        f'''theorem repairedBound{n}_correct :
    (rawBound{n}:ℝ) + ((maxCount{n}:ℝ)-1) *
      ((eta{n}:ℝ) + (epsilon{n}:ℝ)*(repairDiagonal{n}:ℝ)) = (repairedBound{n}:ℝ) := by
  norm_num [rawBound{n},maxCount{n},eta{n},epsilon{n},repairDiagonal{n},repairedBound{n}]''',
        f'#print axioms rawBound{n}_correct', f'#print axioms repairedBound{n}_correct',
        'end D4Bound.SphericalSurplusSign']
    text = '\n\n'.join(lines) + '\n'
    path = OUT / f'SphericalSurplusSignBounds{n}.lean'
    if args.check:
        assert path.read_text() == text
    else:
        path.write_text(text)
    print(path.name, len(text))
