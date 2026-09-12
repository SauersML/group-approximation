"""Exact certification: the C=1 twisted-Weyl linearized system has zero kernel.

Space: V_B = lambda(B)-commutant inside End(l^2 G), G = SL_3(F_2),
B = upper unipotent (order 8).  Exact basis: B-orbit sums
E_(g,h) = sum_b e_(bg,bh), indexed by B-orbits on G x G (diagonal left
mult); dim = |G|^2/|B| = 3528 (all orbits free since left mult is free).

Constraints (tangent system at W = 1):
  (A) (1 + Ad lam(s13)) X = 0
  (B) (1 - Ad lam(s23) - Ad lam(s12)) X = 0
with Ad lam(s) e_(x,y) = e_(sx,sy) (pure permutations mod 2).

Certificate: the stacked constraint matrix on the 3528-dim basis has
full column rank mod p (random prime)  ==>  rank over Q is full  ==>
ker over C is zero (the operators are defined over Q).
"""
import numpy as np

def mod2(t):
    return tuple(tuple(v % 2 for v in row) for row in t)

def mm(x, y):
    return tuple(tuple(sum(x[r][k] * y[k][c] for k in range(3)) % 2
                       for c in range(3)) for r in range(3))

def elem(i, j):
    m = [[1 if r == c else 0 for c in range(3)] for r in range(3)]
    m[i][j] = 1
    return tuple(tuple(row) for row in m)

# enumerate G
gens = [elem(0, 1), elem(0, 2), elem(1, 2), elem(1, 0), elem(2, 0), elem(2, 1)]
ident = tuple(tuple(1 if r == c else 0 for c in range(3)) for r in range(3))
els = [ident]
idx = {ident: 0}
frontier = [ident]
while frontier:
    nxt = []
    for t in frontier:
        for g in gens:
            u = mm(t, g)
            if u not in idx:
                idx[u] = len(els); els.append(u); nxt.append(u)
    frontier = nxt
n = len(els)
assert n == 168, n

def act(g):  # left translation as index permutation
    return [idx[mm(g, x)] for x in els]

W12 = mod2([[0, 1, 0], [1, 0, 0], [0, 0, 1]])
W23 = mod2([[1, 0, 0], [0, 0, 1], [0, 1, 0]])
W13 = mod2([[0, 0, 1], [0, 1, 0], [1, 0, 0]])
p12, p23, p13 = act(W12), act(W23), act(W13)
borel_gens = [elem(0, 1), elem(0, 2), elem(1, 2)]
# enumerate B
bels = [ident]
bidx = {ident}
frontier = [ident]
while frontier:
    nxt = []
    for t in frontier:
        for g in borel_gens:
            u = mm(t, g)
            if u not in bidx:
                bidx.add(u); bels.append(u); nxt.append(u)
    frontier = nxt
assert len(bels) == 8, len(bels)
bperms = [act(b) for b in bels]

# B-orbits on G x G: orbit of (g,h) = {(bg, bh)}; free => 3528 orbits.
orbit_id = {}
orbits = []
for g in range(n):
    for h in range(n):
        if (g, h) in orbit_id:
            continue
        o = len(orbits)
        members = []
        for bp in bperms:
            pr = (bp[g], bp[h])
            orbit_id[pr] = o
            members.append(pr)
        orbits.append(members)
NB = len(orbits)
assert NB == 168 * 168 // 8, NB
print("orbit basis size:", NB, flush=True)

# constraint rows: for each orbit-basis vector E_o, the image under
# (1 + Ad s13) and (1 - Ad s23 - Ad s12) expanded as +-1 combinations of
# ORBIT vectors?  Ad s maps orbit sums to sB s^-1-orbit sums, which are
# unions/redistributions of B-orbit... NOT orbit vectors.  So expand in raw
# matrix units: each raw unit e_(x,y) appears in exactly ONE orbit vector,
# with coefficient 1.  Hence Ad(s) E_o = sum over members (sx, sy), each a
# raw unit = member of a unique orbit BUT only as one of its 8 units.  The
# constraint operators map V_B into the full unit space; expressing rows in
# the raw-unit coordinates is exact.  For rank we need the matrix of the
# stacked operators FROM the orbit basis INTO raw-unit space: column o has
# entries on raw units.  Full column rank of that <=> zero kernel.
prime = 2147483629
# Build columns sparsely: dict from row-key to coeff, rows keyed by
# ("A", x, y) and ("B", x, y).
# For memory, do incremental row reduction with dense rows over the 3528
# columns: rows arrive as sparse (few nonzeros); reduce against pivots.
# Transpose approach: we reduce COLUMN vectors instead: maintain a
# row-echelon basis of the column space inside raw-unit coordinate space.
# Each column has at most 8 + 8 = 16 (A-part) + 24 (B-part) nonzeros.
# Reduction of sparse columns against sparse pivots: keep pivots as dicts.
pivots = {}  # leading raw-unit key -> dict(column vector mod p)

def addmul(vec, other, c):
    for k, v in other.items():
        nv = (vec.get(k, 0) + c * v) % prime
        if nv:
            vec[k] = nv
        elif k in vec:
            del vec[k]

rank = 0
for o in range(NB):
    col = {}
    for (x, y) in orbits[o]:
        # (A): (1 + Ad s13) e = e_(x,y) + e_(p13 x, p13 y)
        for key, c in ((("A", x, y), 1), (("A", p13[x], p13[y]), 1),
                       (("B", x, y), 1), (("B", p23[x], p23[y]), prime - 1),
                       (("B", p12[x], p12[y]), prime - 1)):
            nv = (col.get(key, 0) + c) % prime
            if nv:
                col[key] = nv
            elif key in col:
                del col[key]
    # reduce against existing pivots
    while col:
        lead = min(col)
        if lead in pivots:
            piv = pivots[lead]
            c = (prime - col[lead] * pow(piv[lead], prime - 2, prime)) % prime
            addmul(col, piv, c)
        else:
            pivots[lead] = col
            rank += 1
            break
    else:
        print("KERNEL VECTOR FOUND at orbit", o, flush=True)
        break
    if o % 400 == 0:
        print("processed", o, "rank", rank, flush=True)
print("final rank:", rank, "of", NB, flush=True)
print("CERTIFIED-ZERO-KERNEL" if rank == NB else "KERNEL-NONZERO", flush=True)
