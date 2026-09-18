#!/usr/bin/env python3
"""BFS of the Schreier graph Sch(F/H, {x0^+-1, x1^+-1}), H = Z wr Z, using the
canonical coset representatives of cosets.py.  Writes, for each radius R, the ball
B_R (vertex list with distances) and its edge list with multiplicities (loops kept),
then computes the top eigenvalue of the Dirichlet restriction P_R = 1_B P 1_B
(floating point here; certify_window.py re-checks a rational Rayleigh quotient).

Usage: schreier_bfs.py RMAX
"""
import sys, time, json
import numpy as np
from cosets import *


def main():
    R = int(sys.argv[1])
    t0 = time.time()
    idx = {IDENT: 0}
    reps = [IDENT]
    dist = [0]
    nbr = []  # nbr[v] = list of 4 neighbour indices (or -1 if beyond R)
    frontier = [0]
    sizes = [1]
    for r in range(1, R + 2):
        nf = []
        for v in frontier:
            f = reps[v]
            row = []
            for t in GENS:
                c = canon(comp(t, f))
                w = idx.get(c)
                if w is None:
                    if r > R:
                        row.append(-1)
                        continue
                    w = len(reps)
                    idx[c] = w
                    reps.append(c)
                    dist.append(r)
                    nf.append(w)
                row.append(w)
            nbr.append(row)
        if r > R:
            break
        frontier = nf
        sizes.append(len(nf))
        print(f"r={r} sphere={len(nf)} ball={len(reps)} t={time.time()-t0:.1f}s", flush=True)
    nbr = np.array(nbr, dtype=np.int64)
    np.save(f"nbr_R{R}.npy", nbr)
    np.save(f"dist_R{R}.npy", np.array(dist, dtype=np.int32))
    loops = int(sum(1 for v in range(len(reps)) for w in nbr[v] if w == v))
    json.dump(dict(R=R, spheres=sizes, ball=len(reps), loops=loops,
                   seconds=time.time() - t0), open(f"bfs_R{R}.json", "w"), indent=1)


if __name__ == "__main__":
    main()
