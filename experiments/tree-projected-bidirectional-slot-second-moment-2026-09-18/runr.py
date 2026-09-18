import sys, pickle, time
from engine_r import *
from math import sqrt
J = int(sys.argv[1]); K = int(sys.argv[2]); R = tuple(int(a) for a in sys.argv[3].split(','))
import engine_r; engine_r.POST = tuple(int(a) for a in sys.argv[5].split(",")) if len(sys.argv) > 5 else (0,)
import os; engine_r.NZREF = os.environ.get("NZREF") == "1"; engine_r.RIGID = os.environ.get("RIGID") == "1"; engine_r.RIGID2 = os.environ.get("RIGID2") == "1"
ms = [int(a) for a in sys.argv[4].split(',')]
t0 = time.time()
fn = 'terms_J%d_K%d_R%s_P%s%s.pkl' % (J, K, '_'.join(map(str, R)), '_'.join(map(str, engine_r.POST)), ('_Z1' if engine_r.NZREF else '') + ('_RG' if engine_r.RIGID else '') + ('2' if engine_r.RIGID2 else ''))
try:
    TE, ncl, FM = pickle.load(open(fn, 'rb'))
except Exception:
    TE, ncl = pair_terms(J, K, R, verbose=True)
    FM = first_moment_terms(J, R)
    pickle.dump((TE, ncl, FM), open(fn, 'wb'))
print('J', J, 'K', K, 'R', R, 'terms', len(TE), 'time', round(time.time() - t0, 1), flush=True)
zero = K
def pstar(m, v=2):
    d = 4 * m + v; la = v + 2 * sqrt(3) * m
    return 2 / (la + sqrt(la * la - 4 * (d - 1)))
for m in ms:
    lo, hi = 0.2, 0.6
    for _ in range(20):
        mid = (lo + hi) / 2
        p = F(mid).limit_denominator(10 ** 7) / m
        T = matrix(TE, ncl, m, p)
        w = wblock(FM, m, p); L = 3 * w * w
        lam, _ = rho_phi([[a / L for a in r] for r in T], zero, 150)
        if lam < 1: hi = mid
        else: lo = mid
    ps = F(pstar(m)).limit_denominator(10 ** 9)
    T = matrix(TE, ncl, m, ps); w = wblock(FM, m, ps); L = 3 * w * w
    lam, _ = rho_phi([[a / L for a in r] for r in T], zero, 300)
    print(m, 'm*p_crit', round(hi, 5), 'm*p*', round(m * float(ps), 5), 'rho(p*)', round(lam, 5), 'PASS' if hi < m * float(ps) else 'fail', flush=True)
