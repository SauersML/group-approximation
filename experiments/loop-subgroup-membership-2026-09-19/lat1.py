#!/usr/bin/env python3
"""Level-1 lattice test: image of H=<s,t,u> in Q_1 = G/(G')^X = (Z^3)^X x| M_11.
g -> (V_g, pi_g), V_g(x) = E(g|_x) in Z^3 (E = exponent sums of s,t,u)."""
import sys as _sys, os as _os
_HERE = _os.path.dirname(_os.path.abspath(__file__))
for _d in ('loop-graph-screen-2026-09-18', 'poly-star-obstruction-2026-09-19'):
    _sys.path.insert(0, _os.path.join(_HERE, '..', _d))
import sys
from collections import deque
from poly_star_screen import family
from loopgraph import N, ID, W, reduce, inv, fmt, pmul, pinv

args = sys.argv[1:] or ["chain", "a", "a", "e", "", "", ""]
R = family(*args)
LET = ["s", "t", "u"]
def E(w):
    v = [0, 0, 0]
    for l, e in w:
        if l in LET: v[LET.index(l)] += e
    return tuple(v)
def gen(l):
    p = R.lperm(l, 1)
    V = tuple(E(R.lsec(l, 1, x)) for x in range(N))
    return (V, p)
def mul(A, B):
    VA, pA = A; VB, pB = B
    return (tuple(tuple(VA[x][i] + VB[pA[x]][i] for i in range(3)) for x in range(N)), pmul(pA, pB))
G = [gen(l) for l in LET]
T = {ID: (tuple((0, 0, 0) for _ in range(N)), ID)}
q = deque([ID])
while q:
    p = q.popleft()
    for g in G:
        A = mul(T[p], g)
        if A[1] not in T: T[A[1]] = A; q.append(A[1])
print("root group order", len(T))
# Schreier vectors, fed into incremental HNF
basis = {}  # pivot col -> row (list of ints), rows in echelon form
def insert(v):
    v = list(v)
    while True:
        piv = next((i for i, c in enumerate(v) if c), None)
        if piv is None: return
        if piv not in basis:
            if v[piv] < 0: v = [-c for c in v]
            basis[piv] = v; return
        b = basis[piv]
        # extended gcd combine
        a0, b0 = b[piv], v[piv]
        if b0 % a0 == 0:
            f = b0 // a0; v = [x - f * y for x, y in zip(v, b)]; continue
        # gcd step
        g0, x0, y0 = egcd(a0, b0)
        newb = [x0 * y + y0 * x for x, y in zip(v, b)]
        other = [(b0 // g0) * y - (a0 // g0) * x for x, y in zip(v, b)]
        basis[piv] = newb
        v = other
def egcd(a, b):
    if b == 0: return (a, 1, 0)
    g, x, y = egcd(b, a % b)
    return (g, y, x - (a // b) * y)
cnt = 0
for p, Tp in T.items():
    for g in G:
        A = mul(Tp, g)
        Tq = T[A[1]]
        v = [A[0][x][i] - Tq[0][x][i] for x in range(N) for i in range(3)]
        insert(v); cnt += 1
print("schreier gens", cnt, "rank", len(basis))
det = 1
for k in sorted(basis): det *= basis[k][k]
print("pivots", sorted(basis), "index (if full rank)", det)
print("diag", [basis[k][k] for k in sorted(basis)])
