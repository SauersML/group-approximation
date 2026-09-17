#!/usr/bin/env python3
"""Calibration of signed_monomial_sat.py on the Promislow group P (known answer).

Gardam's complex unit on his 21-element support pair (S, T) has coefficients +-s^i t^j with
s^4 = t^4 = -1 and monomial class rho(a) = s, rho(b) = t (Gardam, arXiv:2312.05240, Remark 2).
The same integer sign problem must therefore be satisfiable for the class (a^4, b^4) = (-1, -1),
and (by the Q-classification gardam-support-pair-has-no-rational-units) unsatisfiable for (1, 1).
Group model and support lists copied from research/artifacts/gardam-support-pair-gsp.py.
"""
from signed_monomial_sat import solve

def mul(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(4)) for j in range(4)) for i in range(4))

def inv(A):
    R = [[A[j][i] for j in range(3)] for i in range(3)]
    t = [A[i][3] for i in range(3)]
    nt = [-sum(R[i][k] * t[k] for k in range(3)) for i in range(3)]
    return tuple(tuple(R[i]) + (nt[i],) for i in range(3)) + ((0, 0, 0, 1),)

E = ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
a = ((1, 0, 0, 1), (0, -1, 0, 1), (0, 0, -1, 0), (0, 0, 0, 1))
b = ((-1, 0, 0, 0), (0, 1, 0, 1), (0, 0, -1, 1), (0, 0, 0, 1))
A_, B_ = inv(a), inv(b)
assert mul(a, A_) == E and mul(b, B_) == E

# letters: element and exponent vector (e_a, e_b)
L = {'a': (a, (1, 0)), 'b': (b, (0, 1))}
def lw(*letters):
    g, e = E, (0, 0)
    for l in letters:
        h, f = L[l]
        g, e = mul(g, h), (e[0] + f[0], e[1] + f[1])
    return g, e
def defl(name, g, e):
    L[name] = (g, e)
defl('x', *lw('a', 'a')); defl('y', *lw('b', 'b')); defl('z', *lw('a', 'b', 'a', 'b'))
defl('X', inv(L['x'][0]), (-2, 0)); defl('Y', inv(L['y'][0]), (0, -2)); defl('Z', inv(L['z'][0]), (-2, -2))

p = [(), ('x', 'Z'), ('X', 'Z'), ('y', 'Z'), ('Y', 'Z')]
q = [('X',), (), ('X', 'Y', 'z'), ('y', 'z')]
r = [('X', 'Y', 'z'), ('x', 'z'), ('Y', 'z', 'z'), ('z', 'z')]
s_ = [('X', 'Z'), ('y', 'Z'), ('Z',), ('X', 'y', 'Z'), ('X', 'Z', 'Z'), ('y', 'Z', 'Z'), ('Z', 'Z'), ('X', 'y', 'Z', 'Z')]
pd = [(), ('X', 'z'), ('x', 'z'), ('y', 'z'), ('Y', 'z')]
qd = [(), ('X',), ('y', 'z'), ('X', 'Y', 'z')]
rd = r
sd = [('X', 'y'), (), ('y',), ('X',), ('X', 'y', 'z'), ('z',), ('y', 'z'), ('X', 'z')]
SW = p + [w + ('a',) for w in q] + [w + ('b',) for w in r] + [w + ('a', 'b') for w in s_]
TW = pd + [w + ('a',) for w in qd] + [w + ('b',) for w in rd] + [w + ('a', 'b') for w in sd]
S = [lw(*w) for w in SW]; T = [lw(*w) for w in TW]
assert len(set(g for g, _ in S)) == 21 and len(set(g for g, _ in T)) == 21
TAB = {}
for i, (g, _) in enumerate(S):
    for j, (h, _) in enumerate(T):
        TAB.setdefault(mul(g, h), []).append((i, j))
data = dict(TAB=TAB, EA=[e for _, e in S], EB=[e for _, e in T], NA=21, NB=21, ONE=E)
for cls in [(-1, -1), (1, 1), (1, -1), (-1, 1)]:
    sols = solve(cls[0], cls[1], True, limit=64, **data)
    print('P calibration class', cls, 'full-support signed-monomial units (sign-normalized):', len(sols))
    if sols:
        print('   first u signs:', sols[0][0])
