import sys, pickle, time
from engine import *
from math import sqrt
J = int(sys.argv[1]); K = int(sys.argv[2]); vert = sys.argv[3] == '1'
ms = [int(a) for a in sys.argv[4].split(',')]
t0 = time.time()
fn = 'terms_J%d_K%d_V%d.pkl' % (J, K, int(vert))
try:
    TE, ncl, FM = pickle.load(open(fn, 'rb'))
except Exception:
    TE, ncl = pair_terms(J, K, vert, verbose=True)
    FM = first_moment_terms(J, vert)
    pickle.dump((TE, ncl, FM), open(fn, 'wb'))
print('J', J, 'K', K, 'vert', vert, 'terms', len(TE), 'time', round(time.time() - t0, 1), flush=True)
zero = K
for m in ms:
    lo, hi = 0.2, 0.6
    for _ in range(20):
        mid = (lo + hi) / 2
        p = F(mid).limit_denominator(10 ** 7) / m
        T = matrix(TE, ncl, m, p)
        w = wblock(FM, m, p); L = 3 * w * w
        Tn = [[a / L for a in r] for r in T]
        lam, _ = rho_phi(Tn, zero, 150)
        if lam < 1: hi = mid
        else: lo = mid
    v = 2; d = 4 * m + v; la = v + 2 * sqrt(3) * m; ps = 2 / (la + sqrt(la * la - 4 * (d - 1)))
    print(m, round(hi, 5), round(m * ps, 5), 'PASS' if hi < m * ps else 'fail', flush=True)
