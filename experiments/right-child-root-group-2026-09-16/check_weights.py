"""Exact check: the generators b^-j s b^j (0 <= j <= n, s in {x, y, x1, y1}) of Lambda_n lie in the depth-monotone
subalgebra R^w_<= = span{S[mu]T[nu] : w(mu) <= w(nu)} for the weight w(0) = 1, w(1) = max(n, 1), and b itself lies
in no R^w_<= and no R^w_>=.

Membership is certified by the canonical form: g = sum over leaves nu, sum over mu in F_nu of S[mu]T[nu], and every
such monomial is checked. Usage: python3 check_weights.py [NMAX]
"""
import sys
from support_closure import x, y, x1, y1, b, binv, conj  # noqa: E402  (also re-runs the formula checks)
from leavitt_ops import *

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5

def weight(word, a, bb):
    return a * word.count('0') + bb * word.count('1')

def monomials(g):
    for nu, F in g.items():
        for mu in F:
            yield mu, nu

def in_Rle(g, a, bb):
    return all(weight(mu, a, bb) <= weight(nu, a, bb) for mu, nu in monomials(g))

for n in range(0, NMAX + 1):
    a, bb = 1, max(n, 1)
    worst = None
    for j in range(n + 1):
        for name, s in (('x', x), ('y', y), ('x1', x1), ('y1', y1)):
            g = conj(j, s)
            ok = in_Rle(g, a, bb)
            assert ok, ('generator outside R^w_<=', n, j, name, sorted(monomials(g)))
            # slack: min over monomials of w(nu) - w(mu)
            slack = min(weight(nu, a, bb) - weight(mu, a, bb) for mu, nu in monomials(g))
            worst = slack if worst is None else min(worst, slack)
    print('n=%d, weight (1,%d): all %d generators of Lambda_n lie in R^w_<= (min slack %d)'
          % (n, bb, 4 * (n + 1), worst))

# sharpness of the weight: with w(1) = n - 1 (n >= 2), b^-n x b^n is outside R^w_<= for the canonical monomials
for n in range(2, NMAX + 1):
    g = conj(n, x)
    print('n=%d: b^-n x b^n in R^w_<= for weight (1,%d)? %s' % (n, n - 1, in_Rle(g, 1, n - 1)))

# b escapes every one-sided weighted part: S[100]T[10] raises weight by w(0) > 0, S[11]T[110] lowers it by w(0)
mons = set(monomials(b))
assert ('100', '10') in mons and ('11', '110') in mons
print('b contains S[100]T[10] and S[11]T[110]: in no R^w_<= and no R^w_>=')
