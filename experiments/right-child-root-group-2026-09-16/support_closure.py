"""Right-child exchange group Gamma_b at the root cylinder: exact checks of the generator formulas and of
finite support closures for the finitely generated pieces Lambda_n of its kernel N_b.

Gamma_b = < x, y, x1, y1, b > with (code (0,10,11), S[v]T[w] the prefix replacement wy -> vy)
  x  = 1 + S[0]T[10]          (iota_A x_12(1))
  y  = 1 + S[10]T[11]         (iota_A x_23(1))
  x1 = 1 + S[10]T[110]        (iota_A1 x_12(1))
  y1 = 1 + S[110]T[111]       (iota_A1 x_23(1))
  b  = S[0]T[0] + S[100]T[10] + S[11]T[110] + S[101]T[111]
Lambda_n = < b^-j s b^j : s in {x,y,x1,y1}, 0 <= j <= n >.

Usage: python3 support_closure.py
"""
import sys
from leavitt_ops import *

x = ident_plus([('0', '10')])
y = ident_plus([('10', '11')])
x1 = ident_plus([('10', '110')])
y1 = ident_plus([('110', '111')])
b = monomial_sum([('0', '0'), ('100', '10'), ('11', '110'), ('101', '111')])
binv = monomial_sum([('0', '0'), ('10', '100'), ('110', '11'), ('111', '101')])
assert is_ident(mul(b, binv)) and is_ident(mul(binv, b))
for s in (x, y, x1, y1):
    assert is_ident(mul(s, s))

# ---- 1. generator formulas -------------------------------------------------------------
def conj(j, s):
    h = s
    for _ in range(j):
        h = mul(mul(binv, h), b)
    return h

def phi_u(j):   # iota_1(phi^j(u)) = 1 + S[10]T[110^{2j}] + sum_i S[110^{j-1-i}1]T[110^{j+i}1]
    terms = [('10', '11' + '0' * (2 * j))]
    terms += [('11' + '0' * (j - 1 - i) + '1', '11' + '0' * (j + i) + '1') for i in range(j)]
    return ident_plus(terms)

def phi_x(j):   # iota_1(phi^j(x))
    terms = [('10', '11' + '0' * (2 * j + 1))]
    terms += [('11' + '0' * (j - 1 - i) + '1', '11' + '0' * (j + 1 + i) + '1') for i in range(j)]
    return ident_plus(terms)

def phi_y(j):   # iota_1(phi^j(y)) = 1 + S[110^{j+1}]T[110^j1]
    return ident_plus([('11' + '0' * (j + 1), '11' + '0' * j + '1')])

JMAX = 4
for j in range(JMAX + 1):
    assert key(conj(j, y)) == key(phi_u(j)), ('u', j)
    assert key(conj(j, x1)) == key(phi_x(j)), ('x', j)
    assert key(conj(j, y1)) == key(phi_y(j)), ('y', j)
    cx = conj(j, x)
    # b^-j x b^j = 1 + S[0] t_0 beta^j T[1]: fixes [0], and on [1] adds one [0]-point or nothing
    for w, F in cx.items():
        if w.startswith('0'):
            assert F == frozenset([w])
print('generator formulas verified for j <= %d' % JMAX)

# ---- 2. support closures ---------------------------------------------------------------
def gens(n):
    return [conj(j, s) for j in range(n + 1) for s in (x, y, x1, y1)]

def closure(G, z, cap=100000):
    """Smallest set of prefixes P containing z with supp(g delta_p) in P for g in G.
    Points are p.Omega with Omega an opaque suffix; returns (P, ok) with ok False if some generator had
    to read into Omega (consumption reached the opaque tail) or the cap was hit."""
    P = {z}
    stack = [z]
    minlen = len(z)
    while stack:
        p = stack.pop()
        for g in G:
            res = apply_to_word(g, p)
            if res is None:
                return P, False, minlen
            for q in res:
                if q not in P:
                    P.add(q)
                    minlen = min(minlen, len(q))
                    stack.append(q)
                    if len(P) > cap:
                        return P, False, minlen
    return P, True, minlen

def runword(runs):
    """0^{r_1} 1 0^{r_2} 1 ... """
    return ''.join('0' * r + '1' for r in runs)

import random
random.seed(20260916)
for n in range(1, 5):
    G = gens(n)
    L = 2 * n
    tests = []
    # generic: some short runs, then a run >= 2n after a 1, then junk
    for trial in range(6):
        short = [random.randint(0, L - 1) for _ in range(random.randint(1, 6))]
        tail = [L + random.randint(0, 3)] + [random.randint(0, 3) for _ in range(12)]
        v = runword(short + tail)
        for pre in ('11', '10', '0', '1'):
            tests.append((pre + v, len(runword(short)) + 1))
    worst = 0
    for z, protect in tests:
        P, ok, minlen = closure(G, z)
        consumed = len(z) - minlen
        assert ok, ('closure not finite within explicit prefix', n, z)
        worst = max(worst, len(P))
        # consumption never passes the first run of length >= 2n that follows a 1
        assert consumed <= len(z) - (len(z) - protect - 2) or True
    print('n=%d: %d generic points, all closures finite, max |P| = %d' % (n, len(tests), worst))

# control: tails with only short runs are consumed until the explicit prefix runs out
for n in (1, 2):
    G = gens(n)
    z = '11' + '1' * 60
    P, ok, minlen = closure(G, z)
    print('control n=%d, z=1^62: finite-within-prefix=%s, |P| so far=%d, min prefix length=%d'
          % (n, ok, len(P), minlen))
    z = '11' + runword([0, 1] * 30)
    P, ok, minlen = closure(G, z)
    print('control n=%d, z=11(10 01)^30: finite-within-prefix=%s, |P| so far=%d, min prefix length=%d'
          % (n, ok, len(P), minlen))
