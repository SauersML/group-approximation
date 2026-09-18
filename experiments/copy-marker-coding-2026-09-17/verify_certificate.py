"""Exact verification of the p=2 certificate from projection_certificate.py.

1. Solve the p=2 LP, round phi to rationals with denominator 10^6 and clip to [-1/2, 1/2].
2. EXACT check (fractions) of drift(D) = (1/5) sum_{g in B_1} [phi(g D g^-1) - phi(g D)] >= delta_exact
   on the covering constraint list (all canonical D with |D| <= L+2, and one length-(L+3)
   representative per canonical (prefix_{p+1}, suffix_{p+1}) pair).
3. Independent float check without the symmetry reduction or the representative argument:
   the drift over every reduced word D with |D| <= NMAX.
Run: python3 verify_certificate.py [NMAX]
"""
import sys
from fractions import Fraction
from coded_pair_lp import ball, mul
from conjugation_projection_lp import inv
from projection_certificate import solve, make_type, S, K

p = 2
L = 2 * p + 3
delta, nv, R, tm, res, var, cons = solve(p)
print('LP delta', delta)
x = res.x[:nv]
typ = make_type(p, L)
phi = {}
for tp, i in var.items():
    q = Fraction(round(x[i] * 10**6), 10**6)
    phi[tp] = max(Fraction(-1, 2), min(Fraction(1, 2), q))


def drift(D, val):
    tot = 0
    for g in S:
        tot += val(typ(mul(mul(g, D), inv(g)))) - val(typ(mul(g, D)))
    return tot / K


exact_min = min(drift(D, lambda t: phi[t]) for D in cons)
print('exact min drift on covering list', exact_min, float(exact_min))
print('max |phi|', float(max(abs(v) for v in phi.values())))
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 11
fl = {t: float(v) for t, v in phi.items()}
m = min(drift(D, lambda t: fl[t]) for D in ball(NMAX))
print(f'float min drift over all D in B_{NMAX}', m)
import json
out = {
    'p': p, 'L': L, 'lp_delta': delta, 'exact_min_drift': str(exact_min),
    'float_min_drift_all_words_up_to': [NMAX, m],
    'phi': {'|'.join(t): str(v) for t, v in sorted(phi.items())},
}
with open('certificate_p2.json', 'w') as fh:
    json.dump(out, fh, indent=0)
print('wrote certificate_p2.json with', len(phi), 'types')
