from fbc import tofib, apply, PHI, PHII, red, inv
from fold2 import SG
import sys, time
A, B, Cc, E = tofib('XyxYx'), tofib('Xyyyx' + 'YYY'), tofib('XYxyx'), tofib('xyX' + 'Y')
def pw(u, j):
    for _ in range(abs(j)): u = apply(PHI if j > 0 else PHII, u)
    return u
sgn = int(sys.argv[1]); M = int(sys.argv[2])
As = [A]; Bs = [pw(B, -1), B] if sgn > 0 else [B, pw(B, -1)]
for m in range(0, M + 1):
    if m:
        As.append(pw(As[-1], sgn)); Bs.append(pw(Bs[-1], sgn))
    gens = [Cc, E, pw(E, 1)] + As + Bs
    t0 = time.time(); G = SG()
    for u in gens: G.add_loop(u)
    G.fold(); V, Ed, rk = G.stats()
    print(sgn, m, 'gens', len(gens), 'rank', rk, 'V', V, 'maxlen', max(map(len, gens)), 'OK' if rk == len(gens) else 'NOT INJECTIVE', '%.1fs' % (time.time() - t0), flush=True)
