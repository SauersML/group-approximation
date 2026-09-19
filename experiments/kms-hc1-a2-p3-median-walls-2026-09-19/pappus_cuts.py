#!/usr/bin/env python3
"""Enumerate the local shapes a locally convex two-sided track of X_3 can have at a vertex.

The link L of every vertex of X_3 is the coset graph of the Heisenberg group
U = <x,y> of order 27 (x=E12, y=E23 over F_3): vertices u<x>, u<y>, edge u
joins u<x> and u<y>.  Link edges have length pi/3.

A locally convex two-sided track through a vertex v is (see the claim) a cone
over a set S of link-edge midpoints such that
  (C1) S is the edge cut E(P,Q) of a bipartition V(L) = P u Q;
  (C2) P and Q each induce connected subgraphs (exactly two local sides);
  (C3) any two points of S are at link distance >= pi, i.e. for distinct cut
       edges e,f the minimum distance between an endpoint of e and an endpoint
       of f is >= 2 (S is an induced matching).
We enumerate all bipartitions and report every S satisfying (C1)-(C3), and
also the weaker counts (C1)+(C2) and (C1)+(C3).
"""
import itertools, sys
from collections import deque

def mul(g, h):
    return ((g[0]+h[0]) % 3, (g[1]+h[1]) % 3, (g[2]+h[2]+g[0]*h[1]) % 3)

U = [(i, j, k) for i in range(3) for j in range(3) for k in range(3)]
X, Y = (1, 0, 0), (0, 1, 0)

def coset(u, s):
    c = {u}; w = u
    for _ in range(2):
        w = mul(w, s); c.add(w)
    return frozenset(c)

verts = sorted({coset(u, X) for u in U} | {coset(u, Y) for u in U}, key=sorted)
vid = {c: i for i, c in enumerate(verts)}
edges = [(vid[coset(u, X)], vid[coset(u, Y)]) for u in U]
n = len(verts)
adj = [set() for _ in range(n)]
for a, b in edges:
    adj[a].add(b); adj[b].add(a)
assert n == 18 and len(edges) == 27 and all(len(s) == 3 for s in adj)

def bfs(src):
    d = {src: 0}; q = deque([src])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if y not in d:
                d[y] = d[x]+1; q.append(y)
    return d
D = [bfs(i) for i in range(n)]

def connected(sub):
    sub = set(sub)
    if not sub: return False
    s = next(iter(sub)); seen = {s}; q = [s]
    while q:
        x = q.pop()
        for y in adj[x]:
            if y in sub and y not in seen:
                seen.add(y); q.append(y)
    return seen == sub

cnt12 = cnt13 = 0; good = []
for mask in range(1, 1 << (n-1)):          # vertex n-1 always in Q
    P = [i for i in range(n) if mask >> i & 1]
    Q = [i for i in range(n) if not mask >> i & 1]
    Ps = set(P)
    cut = [e for e in edges if (e[0] in Ps) != (e[1] in Ps)]
    c3 = all(min(D[a][c] for a in e for c in f) >= 2
             for e, f in itertools.combinations(cut, 2))
    c2 = connected(P) and connected(Q)
    cnt12 += c2; cnt13 += c3
    if c2 and c3:
        good.append((len(P), len(cut), P))
print("vertices", n, "edges", len(edges))
print("bipartitions with (C1)+(C2) [two local sides]:", cnt12)
print("bipartitions with (C1)+(C3) [locally geodesic]:", cnt13)
print("bipartitions with (C1)+(C2)+(C3):", len(good))
for g in good[:20]:
    print("  |P|=%d |S|=%d P=%s" % g)

# Bend profile of the two-sided local shapes.  The angle between the median
# directions of cut edges e != f is (pi/3)*(1 + min endpoint distance), capped
# at pi.  For every bipartition with (C1)+(C2) record the smallest angle and
# the number of pairs at angle < pi ("bent pairs").
from collections import Counter
minang = Counter(); bent = Counter(); best = None
for mask in range(1, 1 << (n-1)):
    Ps = {i for i in range(n) if mask >> i & 1}
    Q = [i for i in range(n) if i not in Ps]
    if not (connected(Ps) and connected(Q)):
        continue
    cut = [e for e in edges if (e[0] in Ps) != (e[1] in Ps)]
    angs = [min(3, 1 + min(D[a][c] for a in e for c in f))
            for e, f in itertools.combinations(cut, 2)]
    m = min(angs); nb = sum(1 for x in angs if x < 3)
    minang[m] += 1; bent[nb] += 1
    if best is None or nb < best[0]:
        best = (nb, len(cut), sorted(Ps))
print("two-sided cuts by smallest angle (units of pi/3):", dict(sorted(minang.items())))
print("fewest bent pairs: %d (|S|=%d, P=%s)" % best)
print("distribution of #bent pairs (first 8):", sorted(bent.items())[:8])

# General local shapes, allowing the wall to run along edges of X_3.  A
# direction of S may be a link vertex a (W contains the edge of X_3 in that
# direction) or a link-edge midpoint m_e (an altitude).  Local convexity:
# pairwise link distance >= pi, i.e. vertex-vertex distance >= 3, vertex-edge
# min endpoint distance >= 3 (pi/6 + (pi/3)d >= pi), edge-edge >= 2.  Sides:
# 2-colour the components of L \ S so that the two ends of every e in M differ
# and the three neighbours of every a in A are not all equal (points of W on
# the edge must touch both halfspaces).  Count every nonempty S admitting it.
pts = [('v', i) for i in range(n)] + [('e', j) for j in range(len(edges))]
def far(p, q):
    ends = lambda r: [r[1]] if r[0] == 'v' else list(edges[r[1]])
    d = min(D[x][y] for x in ends(p) for y in ends(q))
    return d >= (2 if p[0] == q[0] == 'e' else 3)
allS = []
def grow(cur, start):
    if cur: allS.append(list(cur))
    for k in range(start, len(pts)):
        if all(far(pts[k], q) for q in cur):
            cur.append(pts[k]); grow(cur, k+1); cur.pop()
grow([], 0)
ok = 0
for Sx in allS:
    A = {q[1] for q in Sx if q[0] == 'v'}; M = {q[1] for q in Sx if q[0] == 'e'}
    comp = {}; c = 0
    for s in range(n):
        if s in A or s in comp: continue
        comp[s] = c; st = [s]
        while st:
            x = st.pop()
            for j, (u, w) in enumerate(edges):
                if j in M or x not in (u, w): continue
                y = w if x == u else u
                if y not in A and y not in comp:
                    comp[y] = c; st.append(y)
        c += 1
    for col in range(1 << c):
        C = lambda x: col >> comp[x] & 1
        if all(C(edges[j][0]) != C(edges[j][1]) for j in M) and \
           all(len({C(y) for y in adj[a]}) == 2 for a in A):
            ok += 1; print("  admissible S:", Sx); break
print("convex local shapes (edges allowed): %d candidate S, %d admissible" % (len(allS), ok))
