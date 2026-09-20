"""MSI-only bounded extraction of an exact polynomial unit-ideal certificate."""
from pathlib import Path
import json
import runpy
import time

started = time.monotonic()
out = Path('/projects/standard/hsiehph/sauer354/hrf-breakthrough-2026-09-20-sym4')
data = runpy.run_path(str(out/'probe.py'))
R, I = data['R'], data['I']
coefficients = R.one().lift(I)
assert len(coefficients) == len(I.gens())
assert sum(h*f for h, f in zip(coefficients, I.gens())) == 1


def encode_poly(polynomial):
    terms = []
    for exponent, coefficient in polynomial.dict().items():
        scalar = list(map(int, coefficient.polynomial().list()))
        scalar += [0]*(2-len(scalar))
        terms.append([list(map(int, exponent)), scalar])
    return terms


certificate = {'prime': 19, 'quadratic_relation': 'z^2=4z-1',
               'variables': list(R.variable_names()),
               'equations': [encode_poly(f) for f in I.gens()],
               'multipliers': [encode_poly(h) for h in coefficients]}
(out/'certificate.json').write_text(json.dumps(certificate, separators=(',', ':'))+'\n')
print('CERTIFICATE', json.dumps({'elapsed_seconds': time.monotonic()-started,
      'equation_terms': sum(map(len, certificate['equations'])),
      'multiplier_terms': sum(map(len, certificate['multipliers'])),
      'sage_identity_verified': True}), flush=True)
