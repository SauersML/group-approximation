"""Sanity tests for periodic_rips.py."""
import time, random, math
from periodic_rips import *

# S^2 x R: strong product of the octahedron graph with the path Z.
anti = {0: 3, 1: 4, 2: 5, 3: 0, 4: 1, 5: 2}
adj = [set() for _ in range(6)]
for a in range(6):
    for b in range(6):
        if anti[a] == b:
            continue
        for s in (-1, 0, 1):
            if a == b and s == 0:
                continue
            adj[a].add((b, s))
print("S2xR (expect lam=1: [1,1,1], else [0,0,0]):", twisted_betti(6, adj, [1, 12345, P - 1]))

# random planar periodic pattern
random.seed(1)
motif = [(random.uniform(0, 2), random.uniform(0, 1.5)) for _ in range(10)]
t = time.time()
k, adj, m = periodic_graph_from_points(motif, (2, 0), 1.0)
print("rand:", twisted_betti(k, adj, [1, 777, P - 1]), round(time.time() - t, 2))
