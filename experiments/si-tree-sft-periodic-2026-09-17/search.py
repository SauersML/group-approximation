"""Search for SI nearest-neighbour F_2-SFTs without periodic points.

Mode 'random': random relation pairs; every SI pair is checked for a periodic point (sanity).
Mode 'threshold': random (w, phi, psi); the threshold pair is maximal among pairs without
periodic points that it contains, and SI is upward closed, so an SI pair without periodic
points exists iff some threshold pair is SI (after restriction to essential symbols).
"""
import random
import sys
from treesft import essential, is_si, periodic, threshold_pair, show, restrict

mode = sys.argv[1]
n = int(sys.argv[2])
trials = int(sys.argv[3])
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
rng = random.Random(seed)

if mode == "random":
    si = 0
    bad = 0
    for _ in range(trials):
        p = rng.uniform(0.3, 0.9)
        Ra = [sum(1 << t for t in range(n) if rng.random() < p) for s in range(n)]
        Rb = [sum(1 << t for t in range(n) if rng.random() < p) for s in range(n)]
        E = essential(Ra, Rb, n)
        if E == 0 or not is_si(Ra, Rb, n, E):
            continue
        si += 1
        Ra2, Rb2 = restrict(Ra, E, n), restrict(Rb, E, n)
        if not periodic(Ra2, Rb2, n):
            bad += 1
            print("SI WITHOUT PERIODIC POINT", show(Ra2, n), "|", show(Rb2, n))
    print(f"random n={n}: trials={trials} SI={si} SI-without-periodic={bad}")
elif mode == "threshold":
    best = None
    nonempty = 0
    for _ in range(trials):
        w = [rng.gauss(0, 1) for _ in range(n)]
        phi = [rng.gauss(0, rng.choice([0.5, 1, 3])) for _ in range(n)]
        psi = [rng.gauss(0, rng.choice([0.5, 1, 3])) for _ in range(n)]
        Ra, Rb = threshold_pair(w, phi, psi)
        E = essential(Ra, Rb, n)
        if E == 0:
            continue
        nonempty += 1
        if periodic(restrict(Ra, E, n), restrict(Rb, E, n), n):
            print("THEORY VIOLATION: threshold pair has periodic point", w, phi, psi)
            break
        if is_si(Ra, Rb, n, E):
            print("SI WITHOUT PERIODIC POINT", w, phi, psi, show(Ra, n), "|", show(Rb, n), bin(E))
            break
    print(f"threshold n={n}: trials={trials} nonempty={nonempty}")
