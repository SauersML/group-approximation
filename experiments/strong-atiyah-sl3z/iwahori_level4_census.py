#!/usr/bin/env python3
"""Light F_2 check (seconds). V = trace-0 matrices in M_3(F_2), dim 8.
Q1: codim-a subspaces S of V (a = 2, 3) containing none of the 28 rank-2 idempotents.
Q2: which of them are normalized by an order-2^a subgroup of SL_3(F_2) (conjugation).
Matrices are 9-bit ints; functionals y -> tr(c y) with c taken modulo I."""
import itertools

def ent(m, i, j): return (m >> (3 * i + j)) & 1
def mk(f): return sum(1 << (3 * i + j) for i in range(3) for j in range(3) if f(i, j))
MUL = {}
def mul(a, b):
    k = (a, b)
    r = MUL.get(k)
    if r is None:
        r = mk(lambda i, j: sum(ent(a, i, t) & ent(b, t, j) for t in range(3)) & 1)
        MUL[k] = r
    return r
I = mk(lambda i, j: i == j)
def tr(m): return ent(m, 0, 0) ^ ent(m, 1, 1) ^ ent(m, 2, 2)
def det(m):
    a = [[ent(m, i, j) for j in range(3)] for i in range(3)]
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1]) - a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            + a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])) % 2

outer = lambda v, w: mk(lambda i, j: ((v >> i) & 1) & ((w >> j) & 1))
idem2 = sorted({I ^ outer(v, w) for v in range(1, 8) for w in range(1, 8) if bin(v & w).count("1") % 2})
assert len(idem2) == 28

funcs = [c for c in range(1, 512) if c < (c ^ I)]
Z = {c: sum(1 << k for k, e in enumerate(idem2) if tr(mul(c, e)) == 0) for c in funcs}
canon = lambda x: min(x, x ^ I)

def span(cs):
    sp = {0}
    for c in cs:
        sp |= {x ^ c for x in sp}
    return frozenset(canon(x) for x in sp)

G = [m for m in range(512) if det(m) == 1]
assert len(G) == 168
T = {(a, b): mul(a, b) for a in G for b in G}
INV = {a: next(b for b in G if T[(a, b)] == I) for a in G}
def gen(gs):
    H, fr = {I}, [I]
    while fr:
        x = fr.pop()
        for g in gs:
            y = T[(x, g)]
            if y not in H:
                H.add(y); fr.append(y)
    return frozenset(H)
order = {a: len(gen([a])) for a in G}
inv2 = [a for a in G if order[a] == 2]
cyc4 = {gen([a]) for a in G if order[a] == 4}
klein = {gen([a, b]) for a in inv2 for b in inv2 if a != b and T[(a, b)] == T[(b, a)]}
subs4 = cyc4 | klein
subs8 = {gen([a, b]) for a in G for b in G if order[a] in (2, 4) and order[b] in (2, 4) and len(gen([a, b])) == 8}
print("order-4 subgroups:", len(subs4), " order-8 subgroups:", len(subs8))

def normalizes(H, sp):
    return all(canon(mul(mul(INV[u], c), u)) in sp for u in H for c in sp if c)

res = {}
for a in (2, 3):
    found = set()
    for cs in itertools.combinations(funcs, a):
        z = 0x0FFFFFFF
        for c in cs:
            z &= Z[c]
        if z == 0:
            sp = span(cs)
            if len(sp) == 2 ** a:
                found.add(sp)
    subs = subs4 if a == 2 else subs8
    normd = [(sp, H) for sp in found for H in subs if normalizes(H, sp)]
    print(f"a={a}: avoiding codim-{a} subspaces: {len(found)}; normalized by an order-{2**a} subgroup: {len(normd)}")
    res[a] = normd
for sp, H in res[3][:2]:
    print("example a=3 functional span:", sorted(sp), "subgroup size", len(H))
