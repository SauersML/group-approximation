#!/usr/bin/env python3
"""Exhaustive search over F_2 for three-coset units of Gardam's symmetric-piece shape (s0 = 0).

Shape (research/artifacts/promislow-reduced-norm-2026-09-13.md, Section 3): p = x^(1/2)y^(1/2)P0, q = y^(-1/2)Q0,
r = x^(1/2)R0, s = 0, with P0,Q0,R0 invariant under C: (x,y,z) -> (x^-1,y^-1,z).
There, alpha'alpha = N + M ab with N = P0^A P0 - Q0^A Q0 - R0^A R0 and, at s0 = 0,
M = -x^(-1/2)y^(-1/2)(Q0 R0^A + z^-1 Q0^A R0); and det = N^2 - xyz M^2.  So u is a unit iff M = 0 and N in F_2^x = {1}.
Coordinates: doubled x,y exponents, integer z exponent.  Classes: P0 (odd,odd), Q0 (even,odd), R0 (odd,even).
Search space: P0, Q0, R0 unions of C-orbits of monomials in the boxes below.  Each found solution is re-verified
independently with engine.det_right_mult (mod 2) on the assembled element.
"""
import sys, itertools, json
from collections import defaultdict
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from engine import assemble, det_right_mult

KZ = [int(t) for t in sys.argv[1].split(',')] if len(sys.argv) > 1 else [-1, 0, 1]
def orbits(pairs):
    seen, out = set(), []
    for (i, j) in pairs:
        for k in KZ:
            o = frozenset({(i, j, k), (-i, -j, k)})
            if o not in seen:
                seen.add(o); out.append(o)
    return out
odd = [-3, -1, 1, 3]
P_pairs = [(i, j) for i in odd for j in odd if abs(i) + abs(j) <= 4]
Q_pairs = [(i, j) for i in [-2, 0, 2] for j in [-1, 1]]
R_pairs = [(i, j) for i in [-1, 1] for j in [-2, 0, 2]]
PO, QO, RO = orbits(P_pairs), orbits(Q_pairs), orbits(R_pairs)
def tw(c, m):
    s = {'A': (1, -1, -1), 'B': (-1, 1, -1), 'C': (-1, -1, 1)}[c]
    return (s[0] * m[0], s[1] * m[1], s[2] * m[2])
def mul2(f, g):
    out = defaultdict(int)
    for a in f:
        for b in g:
            out[(a[0] + b[0], a[1] + b[1], a[2] + b[2])] ^= 1
    return frozenset(k for k, v in out.items() if v)
def A(f):
    return frozenset(tw('A', m) for m in f)
def subsets(orbs):
    n = len(orbs)
    for mask in range(1, 1 << n):
        s = set()
        for i in range(n):
            if mask >> i & 1:
                s |= orbs[i]
        yield frozenset(s)
# norms of P0
normP = defaultdict(list)
for P0 in itertools.chain([frozenset()], subsets(PO)):
    normP[mul2(P0, A(P0))].append(P0)
ONE = frozenset({(0, 0, 0)})
Zi = frozenset({(0, 0, -1)})
sols = []
Qs = [frozenset()] + list(subsets(QO))
Rs = [frozenset()] + list(subsets(RO))
QQ = {Q0: mul2(Q0, A(Q0)) for Q0 in Qs}
RR = {R0: mul2(R0, A(R0)) for R0 in Rs}
nM0 = 0
for Q0 in Qs:
    QA = A(Q0)
    for R0 in Rs:
        if mul2(Q0, A(R0)) != mul2(Zi, mul2(QA, R0)):
            continue
        nM0 += 1
        rhs = ONE ^ QQ[Q0] ^ RR[R0]
        for P0 in normP.get(rhs, []):
            sols.append((P0, Q0, R0))
def to_pieces(P0, Q0, R0):
    # p = x^(1/2) y^(1/2) P0 etc; convert doubled exponents to integer exponents
    p = {((m[0] + 1) // 2, (m[1] + 1) // 2, m[2]): 1 for m in P0}
    q = {(m[0] // 2, (m[1] - 1) // 2, m[2]): 1 for m in Q0}
    r = {((m[0] + 1) // 2, m[1] // 2, m[2]): 1 for m in R0}
    return p, q, r
nontriv, verified = [], 0
for P0, Q0, R0 in sols:
    p, q, r = to_pieces(P0, Q0, R0)
    D = det_right_mult(assemble(p, q, r), mod=2)
    if D == {(0, 0, 0): 1}:
        verified += 1
    if len(p) + len(q) + len(r) > 1:
        nontriv.append((sorted(p), sorted(q), sorted(r), D == {(0, 0, 0): 1}))
print(json.dumps({'z_range': KZ, 'P0_orbits': len(PO), 'Q0_orbits': len(QO), 'R0_orbits': len(RO),
                  'pairs_with_M0': nM0, 'solutions': len(sols), 'verified_units': verified, 'nontrivial': len(nontriv)}))
for t in nontriv[:10]:
    print('NONTRIVIAL', t)
