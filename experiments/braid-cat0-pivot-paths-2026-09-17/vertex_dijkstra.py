"""Multi-pivot vertex paths between P = {12,34,...} and rho P in the diagonal link X_n.

Graph: proper noncrossing partitions; u ~ v when some noncrossing spanning tree (X-apartment) contains both, with
weight d_B(u, v) (the geodesic segment lies in that apartment, hence in X_n). Dijkstra gives an upper bound for d_X.
"""
import sys, math, heapq, time
from ncp_lib import *

n = int(sys.argv[1]); m = n - 1
t0 = time.time()
P_all = [p for p in set_partitions(n) if is_noncrossing(p)]
idx = {p: i for i, p in enumerate(P_all)}
ZERO, ONE = tuple(range(n)), tuple([0] * n)
V = [i for i, p in enumerate(P_all) if p not in (ZERO, ONE)]
trees = noncrossing_trees(n)
mem = [0] * len(P_all)
for t, T in enumerate(trees):
    for q in tree_flats(T, n):
        mem[idx[q]] |= 1 << t
print('n', n, 'trees', len(trees), round(time.time() - t0, 1), flush=True)


def cosd(x, z):
    a, b = rank(x), rank(z)
    k = n - nblocks(x) - nblocks(z) + nblocks(join_P(x, z))
    return (k - a * b / m) / math.sqrt((a - a * a / m) * (b - b * b / m))


def pairs_partition(shift):
    return canon([((2 * t + shift) % n, (2 * t + 1 + shift) % n) for t in range(n // 2)], n)


P, Q = idx[pairs_partition(0)], idx[pairs_partition(1)]
adj = {i: [] for i in V}
for a in range(len(V)):
    i = V[a]
    for b in range(a + 1, len(V)):
        j = V[b]
        if mem[i] & mem[j]:
            c = cosd(P_all[i], P_all[j])
            if c > -1 + 1e-12:
                d = math.acos(max(-1.0, min(1.0, c)))
                adj[i].append((j, d)); adj[j].append((i, d))
print('graph built', round(time.time() - t0, 1), flush=True)
dist = {P: 0.0}; prev = {}
h = [(0.0, P)]
while h:
    d, u = heapq.heappop(h)
    if d > dist[u]:
        continue
    for v, w in adj[u]:
        if d + w < dist.get(v, 1e9) - 1e-12:
            dist[v] = d + w; prev[v] = u
            heapq.heappush(h, (d + w, v))
path = [Q]
while path[-1] != P:
    path.append(prev[path[-1]])
fmt = lambda p: '{' + ','.join(''.join(str(x + 1) for x in b) for b in blocks(p) if len(b) > 1) + '}'
print('vertex-path distance P -> rho P:', round(dist[Q] / math.pi, 6), 'pi; path', [fmt(P_all[i]) for i in reversed(path)])
