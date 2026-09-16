import sys, time, itertools
import numpy as np
from riphom import vr_betti
from raagcvx import RAAG, ball, hull, dmat, check_isometric

def box(a, b):
    pts = [(i, j) for i in range(a) for j in range(b)]
    return np.array([[abs(p[0]-q[0]) + abs(p[1]-q[1]) for q in pts] for p in pts], float)

def report(name, D, ts, maxdim, coeffs=(2,)):
    for t in ts:
        for c in coeffs:
            t0 = time.time()
            b = vr_betti(D, t, maxdim=maxdim, coeff=c)
            print(f"{name} n={D.shape[0]} diam={int(D.max())} t={t} Z/{c} reduced betti {b}  ({time.time()-t0:.1f}s)", flush=True)

which = sys.argv[1]
md = int(sys.argv[2]) if len(sys.argv) > 2 else 2
ts = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else [1,2,3,4,5,6]
if which.startswith('box'):
    a, b = map(int, which[3:].split('x'))
    report(which, box(a, b), ts, md)
elif which.startswith('raag'):
    # raagNAME:R  NAME in P4, C5, F2xZ, Z2*Z, K1*P4
    name, R = which[4:].split(':'); R = int(R)
    graphs = {'P4': (4, [(0,1),(1,2),(2,3)]), 'C5': (5, [(0,1),(1,2),(2,3),(3,4),(4,0)]),
              'F2xZ': (3, [(0,2),(1,2)]), 'Z2*Z': (3, [(0,1)]), 'K1*P4': (5, [(0,1),(1,2),(2,3),(4,0),(4,1),(4,2),(4,3)]),
              'Z2': (2, [(0,1)]), 'Z3': (3, [(0,1),(1,2),(0,2)]), 'P3': (3, [(0,1),(1,2)])}
    n, E = graphs[name]; G = RAAG(n, E)
    B = ball(G, R); K = hull(G, B); K, D = dmat(G, K)
    print(name, 'R', R, 'ball', len(B), 'hull', len(K), 'badiso', check_isometric(G, K, D), flush=True)
    report(which, D, ts, md)
