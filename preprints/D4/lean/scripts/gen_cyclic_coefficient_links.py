"""Generate exact unshifted first-piece Gram coefficient identities.

These are untrusted rational inputs until each emitted Lean equality compiles.
The only mathematical inputs are the shipped concrete V7 kernel JSON.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as Q
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def exact(x):
    if isinstance(x, bool) or not isinstance(x, (int, str, Q)):
        raise ValueError('coefficient must be an exact integer or rational string')
    return Q(x)


def add(p, q):
    out = dict(p)
    for e, c in q.items():
        out[e] = out.get(e, Q(0)) + c
        if not out[e]:
            del out[e]
    return out


def scale(c, p):
    return {e: c*a for e, a in p.items() if c*a}


def mul(p, q):
    out = {}
    for e, a in p.items():
        for f, b in q.items():
            g = tuple(x+y for x, y in zip(e, f))
            out[g] = out.get(g, Q(0)) + a*b
    return {e: a for e, a in out.items() if a}


def power(p, n):
    out = {(0, 0, 0): Q(1)}
    for _ in range(n):
        out = mul(out, p)
    return out


ONE = {(0, 0, 0): Q(1)}
X, Y, Z = [{tuple(int(j == i) for j in range(3)): Q(1)} for i in range(3)]


def radial(v, ab, variable):
    if len(ab) != 2:
        raise ValueError('radial interval must have two endpoints')
    a, b = map(exact, ab)
    if b <= a:
        raise ValueError('radial interval must have positive width')
    z = scale(1/(b-a), add(variable, scale(-a, ONE)))
    one_z = add(ONE, scale(-1, z))
    out = {}
    for i in range(7):
        out = add(out, scale(exact(v[i])*comb(6, i), mul(power(z, i), power(one_z, 6-i))))
    return out


def radial_block(kd, ell):
    out = {}
    for row in kd['blocks'][ell]['rays']:
        if type(row['weight']) is not int or row['weight'] <= 0:
            raise ValueError('Gram ray weight must be a positive integer')
        v = row['vector'][1:] if ell == 0 else row['vector']
        assert len(v) == 49
        out = add(out, scale(exact(row['weight']), mul(radial(v, kd['radial_basis_intervals'][0], X),
                                                  radial(v, kd['radial_basis_intervals'][0], Y))))
    return out


def homogeneous(n, a, b):
    u, v = ONE, scale(Q(2), a)
    if n == 0:
        return u
    for _ in range(1, n):
        u, v = v, add(scale(Q(2), mul(a, v)), scale(Q(-1), mul(power(b, 2), u)))
    return v


def qlit(q):
    if q.denominator == 1:
        return f'({q.numerator} : ℚ)'
    return f'({q.numerator}/{q.denominator} : ℚ)'


def literal(p):
    return '[\n' + ',\n'.join(f'  (({e[0]},{e[1]},{e[2]}),{qlit(c)})' for e, c in sorted(p.items())) + '\n]'


def generate(kd, ell):
    assert 0 <= ell <= 18 and kd['angular_degree'] == 18 and kd['local_degree'] == 6
    assert len(kd['blocks']) == 19 and len(kd['radial_basis_intervals']) == 7
    assert exact(kd['common_denominator']) > 0
    p = radial_block(kd, ell)
    b = scale(Q(2), mul(mul(X, Y), Z))
    a = mul(add(add(power(X, 2), power(Y, 2)), scale(Q(-1), power(Z, 2))), Z)
    block = scale(Q(1)/(exact(kd['common_denominator'])*(ell+1)),
                  mul(mul(power(b, 18-ell), homogeneous(ell, a, b)), p))
    lines = ['import D4Bound.V7CyclicPolynomialDef',
             'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
             'set_option Elab.async false', 'namespace D4Bound.V7.CyclicPoly.Coeff',
             f'def radial{ell} : Poly := {literal(p)}',
             f'theorem radial{ell}_eq : gramRadial {ell} 0 0 (coordinate 0) (coordinate 1) = radial{ell} := by',
             '  decide +kernel',
             f'def block{ell} : Poly := {literal(block)}',
             f'theorem block{ell}_eq : gramBlock {ell} 0 0 (coordinate 0) (coordinate 1)',
             '    (fullNumerator (coordinate 0) (coordinate 1) (coordinate 2))',
             f'    (fullFactor (coordinate 0) (coordinate 1) (coordinate 2)) = block{ell} := by',
             f'  rw [gramBlock,radial{ell}_eq]', '  decide +kernel',
             f'#print axioms block{ell}_eq', 'end D4Bound.V7.CyclicPoly.Coeff']
    return '\n'.join(lines)+'\n', p, block


def extra_components(kd, od):
    b = scale(Q(2), mul(mul(X, Y), Z))
    a = mul(add(add(power(X, 2), power(Y, 2)), scale(Q(-1), power(Z, 2))), Z)
    spherical = {}
    for row in od['appended_spherical_local_energy_rays']:
        assert exact(row['R']) >= exact(kd['breaks'][1])
        for ell, coefficient in enumerate(row['scalar_coefficients']):
            spherical = add(spherical, scale(-exact(row['weight'])*exact(coefficient)/(ell+1),
                mul(power(b, 18-ell), homogeneous(ell, a, b))))
    count = Q(0)
    for row in [dict(od['nested_count_quadratic'], weight=1)]+od['conditional_count_polynomials']:
        n = len(row['radii'])
        assert all(exact(R) >= exact(kd['breaks'][1]) for R in row['radii'])
        k = 1+n
        for i in range(n):
            for j in range(i, n):
                count += exact(row['weight'])*exact(row['coefficients'][k])*(1 if i == j else 2)
                k += 1
    for row in od['conditional_radial_rays']:
        assert exact(row['inner_radius']) >= exact(kd['breaks'][1])
        assert exact(row['outer_radius']) >= exact(kd['breaks'][1])
    return spherical, count, add(spherical, scale(count, power(b, 18)))


def complete_polynomial(kd, od):
    blocks = [generate(kd, ell)[2] for ell in range(19)]
    _, _, pair = extra_components(kd, od)
    for p in blocks:
        pair = add(pair, p)
    swap_yz = {(i, k, j): c for (i, j, k), c in pair.items()}
    cycle = {(k, i, j): c for (i, j, k), c in pair.items()}
    total = add(add(pair, swap_yz), cycle)
    return pair, total


def generate_extra(kd, od):
    spherical, count, extra = extra_components(kd, od)
    lines = ['import D4Bound.V7CyclicPolynomialDef',
             'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
             'set_option Elab.async false', 'namespace D4Bound.V7.CyclicPoly.Coeff',
             f'def sphericalData : Poly := {literal(spherical)}',
             'theorem sphericalData_eq : spherical 0 0',
             '    (fullNumerator (coordinate 0) (coordinate 1) (coordinate 2))',
             '    (fullFactor (coordinate 0) (coordinate 1) (coordinate 2)) = sphericalData := by',
             '  decide +kernel',
             'theorem conditional0_eq : conditional 0 0 = 0 := by decide +kernel',
             'theorem count0_eq : (countPolynomials.map fun c => count c 0 0).sum =',
             f'    {qlit(count)} := by decide +kernel',
             f'def extraData : Poly := {literal(extra)}',
             'theorem extraData_eq : fastAdd sphericalData',
             f'    (scale {qlit(count)} (fastPower (fullFactor (coordinate 0) (coordinate 1) (coordinate 2)) 18)) =',
             '    extraData := by decide +kernel',
             '#print axioms sphericalData_eq', 'end D4Bound.V7.CyclicPoly.Coeff']
    return '\n'.join(lines)+'\n'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--degree', type=int)
    ap.add_argument('--diagnostic', action='store_true')
    ap.add_argument('--extra', action='store_true')
    ap.add_argument('--reference-power', type=Path)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--check', action='store_true')
    a = ap.parse_args()
    kd = json.loads((ROOT/'data/v7/kernel.json').read_text())
    if a.extra:
        if a.degree is not None or a.diagnostic:
            ap.error('--extra is separate from degree and diagnostic modes')
        text = generate_extra(kd, json.loads((ROOT/'data/v7/origin.json').read_text()))
        if a.check:
            if a.out.read_text() != text:
                raise SystemExit('generated source mismatch')
        else:
            a.out.parent.mkdir(parents=True, exist_ok=True)
            a.out.write_text(text)
        print(json.dumps({'status': 'MATCH' if a.check else 'GENERATED_NOT_PROVED',
                          'kind': 'extra', 'source_bytes': len(text.encode())}))
        return
    if a.diagnostic:
        if a.degree is not None or a.check:
            ap.error('diagnostic is separate from degree generation/check')
        od = json.loads((ROOT/'data/v7/origin.json').read_text())
        pair, total = complete_polynomial(kd, od)
        result = {'status': 'COMPUTED_EXACT_NOT_LEAN', 'pair_terms': len(pair), 'cyclic_terms': len(total),
                  'total_degree': max(sum(e) for e in total),
                  'cyclic': [[list(e), str(c)] for e, c in sorted(total.items())]}
        if a.reference_power is not None:
            ref = json.loads(a.reference_power.read_text())
            expected = {tuple(e): Q(c)/Q(ref['denominator']) for e, c in ref['entries']}
            result['reference_exact_equal'] = total == expected
            if total != expected:
                result['differing_terms'] = len(add(total, scale(Q(-1), expected)))
        a.out.parent.mkdir(parents=True, exist_ok=True)
        a.out.write_text(json.dumps(result, separators=(',', ':'))+'\n')
        print(json.dumps({k: v for k, v in result.items() if k != 'cyclic'}))
        return
    if a.degree is None:
        ap.error('--degree is required outside diagnostic mode')
    text, radial_poly, block = generate(kd, a.degree)
    if a.check:
        if a.out.read_text() != text:
            raise SystemExit('generated source mismatch')
    else:
        a.out.parent.mkdir(parents=True, exist_ok=True)
        a.out.write_text(text)
        a.out.with_suffix('.json').write_text(json.dumps({
            'degree': a.degree, 'radial': [[list(e), str(c)] for e, c in sorted(radial_poly.items())],
            'block': [[list(e), str(c)] for e, c in sorted(block.items())]}, separators=(',', ':'))+'\n')
    print(json.dumps({'status': 'MATCH' if a.check else 'GENERATED_NOT_PROVED',
                      'degree': a.degree, 'radial_terms': len(radial_poly), 'block_terms': len(block),
                      'source_bytes': len(text.encode())}))


if __name__ == '__main__':
    main()
