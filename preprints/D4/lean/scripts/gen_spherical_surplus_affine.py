"""Exact degree16 affine basis matrices; every identity is replayed in Lean."""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import importlib.util
import sys

sys.dont_write_bytecode = True
PKG = Path(__file__).resolve().parents[2]
SOURCE = PKG / 'verify/stage2_origin/source'
OUT = PKG / 'lean/D4Bound'
spec = importlib.util.spec_from_file_location('surplus_affine_algebra', SOURCE /
    'optimization/continuation_20261018/base/new_work/spherical_sdp/certify.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
ap = argparse.ArgumentParser()
ap.add_argument('--check', action='store_true')
args = ap.parse_args()
for n, p, q in [(0, 751467, 500000), (1, 61, 40), (2, 303, 200)]:
    T, d = m.transform(16, Q(-1), Q(p, q))
    mat = '![' + ', '.join('![' + ', '.join(str(int(v)) for v in row) + ']'
        for row in T) + ']'
    lines = ['-- Generated exact matrix; no imported correctness flag.',
        'import D4Bound.SphericalSurplusSignTransform16',
        'set_option maxHeartbeats 0', 'set_option Elab.async false',
        'namespace D4Bound.SphericalSurplusSign.Bernstein16',
        f'def affine{n} : I → I → ℤ := {mat}', f'def affineDen{n} : ℤ := {d}',
        f'''lemma affine{n}_exact (j : I) (x : ℝ) :
    (∑ i : I, (affine{n} i j : ℝ) * basis i x) =
      (affineDen{n} : ℝ) * (-1 + ({p} : ℝ) / {q} * x)^j.val := by
  fin_cases j <;> norm_num [affine{n}, affineDen{n}, basis, Fin.sum_univ_succ, Nat.choose] <;> ring''',
        f'#print axioms affine{n}_exact', 'end D4Bound.SphericalSurplusSign.Bernstein16']
    text = '\n\n'.join(lines) + '\n'
    assert len(text.encode()) < 1024**2
    path = OUT / f'SphericalSurplusSignAffine{n}.lean'
    if args.check:
        assert path.read_text() == text
    else:
        path.write_text(text)
    print(path.name, len(text))
