"""Vertex link of X_3 and its geodesic count (input to the no-flat-triplane lemma).

The vertex U = <x,y> (Heisenberg of order 27, x = E_12, y = E_23 in SL_3(F_3)) has link L:
vertices are the cosets u<x> and u<y> (18), edges are the elements u of U (27), joining u<x>, u<y>.
Checks: L is cubic, bipartite, girth 6, diameter 4, distance-regular with intersection array
{3,2,2,1;1,1,2,3} (Pappus graph), and the number of geodesic paths between vertices at distance 3
is exactly 2 for every such pair (so at most 2 internally disjoint paths of length pi exist).
All three vertex groups of Gamma_3 are isomorphic to U with the same pair of generating cyclic
subgroups up to automorphism, so the three vertex links are isomorphic to L."""
import itertools
from collections import deque

def mul(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(3)) % 3 for j in range(3)) for i in range(3))
I = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
x = ((1, 1, 0), (0, 1, 0), (0, 0, 1)); y = ((1, 0, 0), (0, 1, 1), (0, 0, 1))
U = {I}; fr = [I]
while fr:
    nf = []
    for g in fr:
        for s in (x, y):
            h = mul(g, s)
            if h not in U: U.add(h); nf.append(h)
    fr = nf
assert len(U) == 27
def coset(g, s): return frozenset({g, mul(g, s), mul(mul(g, s), s)})
V = sorted({('x', coset(u, x)) for u in U} | {('y', coset(u, y)) for u in U}, key=str)
idx = {v: i for i, v in enumerate(V)}; n = len(V)
adj = [set() for _ in range(n)]
for u in U:
    p, q = idx[('x', coset(u, x))], idx[('y', coset(u, y))]; adj[p].add(q); adj[q].add(p)
assert n == 18 and all(len(a) == 3 for a in adj)
def bfs(s):
    d = [-1] * n; d[s] = 0; cnt = [0] * n; cnt[s] = 1; Qu = deque([s])
    while Qu:
        v = Qu.popleft()
        for w in adj[v]:
            if d[w] < 0: d[w] = d[v] + 1; Qu.append(w)
            if d[w] == d[v] + 1: cnt[w] += cnt[v]
    return d, cnt
diam = 0; arrays = set(); geo3 = set(); girth = 99
for s in range(n):
    d, cnt = bfs(s); diam = max(diam, max(d))
    b = tuple(sum(1 for w in adj[v] if d[w] == d[v] + 1) for v in range(n))
    c = tuple(sum(1 for w in adj[v] if d[w] == d[v] - 1) for v in range(n))
    arr = tuple(sorted({(d[v], b[v], c[v]) for v in range(n)})); arrays.add(arr)
    geo3 |= {cnt[v] for v in range(n) if d[v] == 3}
    for v in range(n):   # girth via BFS: an edge between equal levels or two parents gives a cycle
        if sum(1 for w in adj[v] if d[w] == d[v] - 1) > 1: girth = min(girth, 2 * d[v])
        if any(d[w] == d[v] for w in adj[v]): girth = min(girth, 2 * d[v] + 1)
print("vertices", n, "edges", sum(map(len, adj)) // 2, "diameter", diam, "girth", girth)
print("distance-regular:", len(arrays) == 1, "levels (d, b_d, c_d):", sorted(arrays)[0])
print("number of geodesics between vertices at distance 3:", sorted(geo3))
