# raw (no symmetry reduction) counts of odometer models, for cross-checking against GAP (xcheck.g)
import sys, lift as L, bfs
if len(sys.argv) > 2 and sys.argv[2] == "noR": L.RELS[:] = L.RELS[:4]
lev = [[[0], [0], [0], [0]]]
for k in range(1, int(sys.argv[1]) + 1):
    lev = [n for p in lev for n in bfs.lifts(p)]
    print("level", k, "raw solutions", len(lev), flush=True)
