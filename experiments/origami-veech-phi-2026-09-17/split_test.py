import sys
from perm import *
from wms import B as B8, C as C8
from scaled import scale
from affine import lifts, S_MAT, T_MAT
m = int(sys.argv[1])
b, c = scale(B8, C8, m)
Ss, Ts = lifts(B8, C8, m, S_MAT), lifts(B8, C8, m, T_MAT)
print("m", m, "d", len(b), "#S", len(Ss), "#T", len(Ts))
res = []
for s in Ss:
    for t in Ts:
        tot = {k: perm_rank_defect(v) for k, v in relators(b, c, s, t).items()}
        res.append((max(tot.values()), tot))
res.sort(key=lambda r: r[0])
print("best over all S,T lifts:", res[0])
