"""Census with the exact SI test (half-tree mixing).

  python3 census_exact.py sanity
  python3 census_exact.py random n trials seed      random pairs: count path-mixing, SI, and SI without
                                                   periodic point (the last would answer Poirier-Salo)
  python3 census_exact.py threshold n trials seed   random threshold pairs (never periodic): any SI?
"""
import random
import sys
from treesft import essential, is_si, periodic, restrict, threshold_pair
from si_exact import hm
from bank_sft import build

mode = sys.argv[1]
if mode == "sanity":
    print("full shift n=2: hm =", hm([3, 3], [3, 3], 2))
    print("identity relations n=2 (not SI): hm =", hm([1, 2], [1, 2], 2))
    syms, Ra, Rb = build(4, 2, 2)
    n = len(syms)
    E = essential(Ra, Rb, n)
    print("bank K=4 c=d=2: path mixing", is_si(Ra, Rb, n, E), " hm =", hm(Ra, Rb, n, E))
    sys.exit()

n, trials, seed = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rng = random.Random(seed)
stats = dict(nonempty=0, path=0, si=0, si_nonperiodic=0)
rvals = {}
for _ in range(trials):
    if mode == "random":
        dens = rng.choice([0.3, 0.5, 0.7])
        Ra = [sum(1 << t for t in range(n) if rng.random() < dens) for _ in range(n)]
        Rb = [sum(1 << t for t in range(n) if rng.random() < dens) for _ in range(n)]
    else:
        w = [rng.gauss(0, 1) for _ in range(n)]
        phi = [rng.gauss(0, rng.choice([.5, 1, 3])) for _ in range(n)]
        psi = [rng.gauss(0, rng.choice([.5, 1, 3])) for _ in range(n)]
        Ra, Rb = threshold_pair(w, phi, psi)
    E = essential(Ra, Rb, n)
    if E == 0:
        continue
    stats["nonempty"] += 1
    if not is_si(Ra, Rb, n, E):
        continue
    stats["path"] += 1
    r = hm(Ra, Rb, n, E)
    if r is None:
        continue
    stats["si"] += 1
    rvals[r] = rvals.get(r, 0) + 1
    if not periodic(restrict(Ra, E, n), restrict(Rb, E, n), n):
        stats["si_nonperiodic"] += 1
        print("SI WITHOUT PERIODIC POINT:", Ra, Rb, bin(E))
print(mode, n, stats, "HM constants", dict(sorted(rvals.items())))
