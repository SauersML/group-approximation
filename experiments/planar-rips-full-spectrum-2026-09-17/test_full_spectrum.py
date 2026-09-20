"""Validation of full_spectrum.py on abstract periodic flag complexes."""
import random
from full_spectrum import h2_spectrum
from periodic_rips import periodic_graph_from_points, reduce_periodic


def strong_product(anti, perm):
    """Octahedron x Z strong product; step j -> j+1 applies perm."""
    adj = [set() for _ in range(6)]
    for a in range(6):
        for b in range(6):
            if b != anti[a] and a != b:
                adj[a].add((b, 0))
            # (a, j) ~ (perm-image, j+1): (a,j) adjacent to (b,j+1) iff
            # b is not antipodal to perm[a]... closed nbhd of perm[a]
            if b != anti[perm[a]]:
                adj[a].add((b, 1))
                adj[b].add((a, -1))
    return adj


anti = {0: 3, 1: 4, 2: 5, 3: 0, 4: 1, 5: 2}
ident = {i: i for i in range(6)}
swap = {0: 3, 3: 0, 1: 1, 4: 4, 2: 2, 5: 5}  # orientation-reversing
print("S2xR (expect torsion t-1):", h2_spectrum(6, strong_product(anti, ident)))
print("S2 x~ R (expect torsion t+1):", h2_spectrum(6, strong_product(anti, swap)))

random.seed(1)
motif = [(random.uniform(0, 2), random.uniform(0, 1.5)) for _ in range(10)]
k, adj, m = periodic_graph_from_points(motif, (2, 0), 1.0)
print("rand planar:", h2_spectrum(k, adj))
k2, adj2, _ = reduce_periodic(k, adj)
print("rand planar reduced:", h2_spectrum(k2, adj2))
