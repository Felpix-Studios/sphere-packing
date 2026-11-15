"""Strict schemas for the exact data consumed by the Gram Lean exporters."""
from fractions import Fraction


def rational(value):
    if isinstance(value, (bool, float)):
        raise ValueError('Expected an exact rational, not a Boolean or float')
    if not isinstance(value, (str, int, Fraction)):
        raise ValueError('Expected an integer or rational string')
    return Fraction(value)


def integer(value):
    q = rational(value)
    if q.denominator != 1:
        raise ValueError('Nonintegral value in integer witness data')
    return q.numerator


def vector(values, size, parse=rational):
    if not isinstance(values, list) or len(values) != size:
        raise ValueError(f'Expected a list of length {size}')
    return [parse(x) for x in values]


def matrix(values, rows, cols):
    if not isinstance(values, list) or len(values) != rows:
        raise ValueError(f'Expected {rows} matrix rows')
    return [vector(row, cols) for row in values]


def validate_kernel(kernel):
    if integer(kernel['common_denominator']) <= 0:
        raise ValueError('Gram denominator must be positive')
    rays = kernel['blocks'][0]['rays']
    if not isinstance(rays, list) or len(rays) != 34:
        raise ValueError('Expected 34 degree-zero rays')
    keys = []
    for ray in rays:
        if integer(ray['weight']) < 0:
            raise ValueError('Negative Gram weight')
        v = vector(ray['vector'], 50, integer)
        keys.append(v[1])
    if len(set(keys)) != 34:
        raise ValueError('Duplicate first-coordinate ray lookup key')


RADIAL_ENDPOINTS = list(map(Fraction, [
    '1', '501473/500000', '1005643/1000000', '50379/50000',
    '50767/50000', '102597/100000', '3/2', '7/4']))


def validate_planes(planes):
    if not isinstance(planes, list) or len(planes) != 12:
        raise ValueError('Expected exactly twelve affine planes')
    for row in planes:
        if integer(row['ray_count']) != 34:
            raise ValueError('Wrong ray count in affine plane')
        vector(row['ray_centers'], 34)
        vector(row['physical_radial_linear_coefficients'], 49)
        rational(row['constant'])
        vector(row['near_shell_lower_bounds'], 5)
        vector(row['affine_count_coefficients'], 5)
        pieces = row['pieces']
        if not isinstance(pieces, list) or len(pieces) != 7:
            raise ValueError('Expected seven radial pieces')
        for i, piece in enumerate(pieces):
            if integer(piece['piece']) != i:
                raise ValueError('Duplicate, missing or out-of-order radial piece')
            if vector(piece['physical_interval'], 2) != RADIAL_ENDPOINTS[i:i+2]:
                raise ValueError('Radial interval does not match the physical selector')
            vector(piece['exact_restricted_Bernstein_coefficients'], 7)
            rational(piece['certified_lower_bound'])


def validate_inputs(kernel, origin, projection, planes):
    validate_kernel(kernel)
    vector(origin['u'], 49)
    matrix(projection['indicator_range_solutions'], 49, 5)
    matrix(projection['D_inverse'], 5, 5)
    vector(projection['count_offsets_m'], 5)
    validate_planes(planes)
