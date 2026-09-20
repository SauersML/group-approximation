"""MSI-only capped pass: all 124 nonzero exponent triples, without symmetry reduction."""
from pathlib import Path
import itertools
import json
import runpy
import time

started = time.monotonic()
out = Path('/projects/standard/hsiehph/sauer354/hrf-breakthrough-2026-09-20-sym4')
data = runpy.run_path(str(out/'probe.py'))
from sage.all import matrix, diagonal_matrix, prod
R, A, B, C, PB, PC, z = [data[s] for s in ('R','A','B','C','PB','PC','z')]
variables = R.gens()
v = [R(1)] + list(variables[:4])
w = [R(1)] + list(variables[4:8])
AR = A.change_ring(R)
PB_inverse, PC_inverse = PB.inverse().change_ring(R), PC.inverse().change_ring(R)
PB, PC = PB.change_ring(R), PC.change_ring(R)
case_dir = out/'cases'
case_dir.mkdir(exist_ok=True)


def shift(exponent):
    return matrix(R, 5, 5, lambda i, j: int(i == (j-exponent) % 5))


def encode_poly(polynomial):
    terms = []
    for exponent, coefficient in polynomial.dict().items():
        scalar = list(map(int, coefficient.polynomial().list()))
        scalar += [0]*(2-len(scalar))
        terms.append([list(map(int, exponent)), scalar])
    return terms


V_choices = [PB*shift(b)*diagonal_matrix(R, v)*PB_inverse for b in range(5)]
W_choices = [PC*shift(c)*diagonal_matrix(R, w)*PC_inverse for c in range(5)]
for b, V in enumerate(V_choices):
    assert V*B.change_ring(R) == z**b*B.change_ring(R)*V
for c, W in enumerate(W_choices):
    assert W*C.change_ring(R) == z**c*C.change_ring(R)*W

triples = [list(t) for t in itertools.product(range(5), repeat=3) if any(t)]
(out/'all-triples.json').write_text(json.dumps(triples)+'\n')
records = []
for a, b, c in triples:
    if time.monotonic()-started > 49:
        print('INTERNAL_TIME_LIMIT', flush=True)
        break
    case_started = time.monotonic()
    U = V_choices[b]*W_choices[c]
    equations = (U*AR-z**a*AR*U).list()+[variables[8]*prod(v+w)-1]
    I = R.ideal(equations)
    label = f'{a}{b}{c}'
    entry = {'triple': [a,b,c], 'equations': [encode_poly(f) for f in equations]}
    (case_dir/f'{label}-input.json').write_text(json.dumps(entry, separators=(',', ':'))+'\n')
    G = I.groebner_basis(algorithm='libsingular:std')
    unit = len(G) == 1 and G[0] == 1
    record = {'triple': [a,b,c], 'unit_ideal': bool(unit), 'certificate_verified': False}
    if unit:
        coefficients = R.one().lift(I)
        assert sum(h*f for h,f in zip(coefficients, equations)) == 1
        certificate = {'prime': 19, 'quadratic_relation': 'z^2=4z-1',
                       'variables': list(R.variable_names()), 'triple': [a,b,c],
                       'equations': entry['equations'],
                       'multipliers': [encode_poly(h) for h in coefficients]}
        (case_dir/f'{label}-certificate.json').write_text(
            json.dumps(certificate, separators=(',', ':'))+'\n')
        record['certificate_verified'] = True
        record['multiplier_terms'] = sum(map(len, certificate['multipliers']))
    else:
        (case_dir/f'{label}-groebner.txt').write_text('\n'.join(map(str, G))+'\n')
        record['basis_length'] = len(G)
    record['seconds'] = time.monotonic()-case_started
    records.append(record)
    (out/'all-results.json').write_text(json.dumps(records, indent=2)+'\n')
    print('CASE', json.dumps(record), flush=True)
print('COVERAGE', json.dumps({'completed': len(records), 'total': len(triples),
      'unit_ideals': sum(r['unit_ideal'] for r in records),
      'elapsed_seconds': time.monotonic()-started}), flush=True)
