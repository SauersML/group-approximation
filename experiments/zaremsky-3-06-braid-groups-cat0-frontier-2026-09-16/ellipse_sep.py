#!/usr/bin/env python3
"""Separation certificate for d_X(x, y) >= pi between two vertices of the diagonal link X_n of |NCP_n|.

Usage: python3 ellipse_sep.py n [x y]      x, y given as block lists like 12,34,56,78 (default: pairs partition
                                           P = {12,34,...} and its rotation rho P = {23,45,...,n1})

Certificate (see research/artifacts/zp-braid-cat0-pivot-obstructions-2026-09-16.md, Lemma E):
  E_vert = { vertex z : m (k(x,z) + k(z,y)) > rk(z) (rk x + rk y) }   (exactly: cos d_B(x,z) + cos d_B(z,y) > 0
  when rk x = rk y; for general ranks the script uses floating point with a margin and reports the margin),
  where m = n - 1 and k(x,z) = dim f(x) cap f(z) = n - b(x) - b(z) + b(x v_Pi z).
  If x and y lie in different connected components of the comparability graph restricted to E_vert,
  every path in X_n from x to y has length >= pi.
Also reports E_vert sizes, whether any universal vertex is in E_vert, and component sizes.
"""
import sys, math
from collections import deque

n = int(sys.argv[1]); m = n - 1
popc = lambda v: bin(v).count("1")
FULL = (1 << n) - 1

def set_partitions(n):
    def rec(i, blocks):
        if i == n:
            yield blocks; return
        for k in range(len(blocks)):
            nb = list(blocks); nb[k] |= (1 << i)
            yield from rec(i + 1, nb)
        yield from rec(i + 1, blocks + [1 << i])
    yield from rec(0, [])

def crossing(b1, b2):
    e = [i for i in range(n) if b1 >> i & 1]
    for j in range(len(e)):
        a, c = e[j], e[(j + 1) % len(e)]
        gap = 0; t = (a + 1) % n
        while t != c:
            gap |= 1 << t; t = (t + 1) % n
        if b2 & ~gap == 0:
            return False
    return True

NC = []
for bl in set_partitions(n):
    nonsing = [b for b in bl if popc(b) >= 2]
    if all(not crossing(nonsing[i], nonsing[j]) for i in range(len(nonsing)) for j in range(i + 1, len(nonsing))):
        NC.append(tuple(sorted(bl)))           # all blocks, singletons included
rk = {p: n - len(p) for p in NC}
proper = [p for p in NC if 0 < rk[p] < m]

def join_blocks(x, y):
    parent = list(range(n))
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]; a = parent[a]
        return a
    for bl in list(x) + list(y):
        e = [i for i in range(n) if bl >> i & 1]
        for t in e[1:]:
            parent[find(t)] = find(e[0])
    return len(set(find(i) for i in range(n)))

def kdim(x, y):
    return n - len(x) - len(y) + join_blocks(x, y)

def leq(x, y):
    return all(any(bx & by == bx for by in y) for bx in x)

def cyc_interval(b):
    for s in range(n):
        for L in range(1, n + 1):
            if sum(1 << ((s + t) % n) for t in range(L)) == b:
                return True
    return False

def universal(p):
    ns = [b for b in p if popc(b) >= 2]
    return len(ns) == 1 and cyc_interval(ns[0])

def parse(s):
    blocks = [sum(1 << (int(ch) - 1) for ch in blk) for blk in s.split(",")]
    cov = 0
    for b in blocks: cov |= b
    return tuple(sorted(blocks + [1 << i for i in range(n) if not cov >> i & 1]))

if len(sys.argv) > 3:
    X, Y = parse(sys.argv[2]), parse(sys.argv[3])
else:
    X = parse(",".join(f"{2*t+1}{2*t+2}" for t in range(n // 2)))
    Y = tuple(sorted(sum(1 << ((i + 1) % n) for i in range(n) if b >> i & 1) for b in X))

def cosd(x, z):
    a, b, k = rk[x], rk[z], kdim(x, z)
    return (k - a * b / m) / math.sqrt((a - a * a / m) * (b - b * b / m))

exact = rk[X] == rk[Y]
Ev, margin = [], float("inf")
for z in proper:
    if exact:
        val = m * (kdim(X, z) + kdim(z, Y)) - rk[z] * (rk[X] + rk[Y])   # sign of cos d(x,z) + cos d(z,y)
        s = cosd(X, z) + cosd(z, Y)
    else:
        s = cosd(X, z) + cosd(z, Y); val = s
    margin = min(margin, abs(s))
    if val > 0:
        Ev.append(z)
Eset = set(Ev)
adj = {z: [w for w in Ev if w != z and (leq(z, w) or leq(w, z))] for z in Ev}
comp, cid = {}, 0
for z in Ev:
    if z in comp: continue
    dq = deque([z]); comp[z] = cid
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if w not in comp:
                comp[w] = cid; dq.append(w)
    cid += 1
sizes = sorted([sum(1 for z in Ev if comp[z] == c) for c in range(cid)], reverse=True)
fmt = lambda p: "{" + ",".join("".join(str(i + 1) for i in range(n) if b >> i & 1) for b in p if popc(b) >= 2) + "}"
print("n =", n, "| x =", fmt(X), "| y =", fmt(Y), "| d_B(x,y) = %.6f pi" % (math.acos(max(-1, min(1, cosd(X, Y)))) / math.pi))
print("#proper vertices:", len(proper), "| #E_vert:", len(Ev), "| exact integer test:", exact,
      "| min |cos d(x,z)+cos d(z,y)| over vertices: %.3g" % margin)
print("universal vertices in E_vert:", [fmt(z) for z in Ev if universal(z)])
print("components:", cid, "sizes:", sizes[:12])
print("x in E_vert:", X in Eset, "| y in E_vert:", Y in Eset)
if X in Eset and Y in Eset:
    print("SEPARATED (certificate d_X(x,y) >= pi):", comp[X] != comp[Y])
    for tag, V in (("x", X), ("y", Y)):
        cx = [fmt(z) for z in Ev if comp[z] == comp[V]]
        print("component of", tag, "(%d):" % len(cx), cx[:40])
