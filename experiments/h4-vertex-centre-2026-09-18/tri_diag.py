"""diagnostic for triangle.py: which condition kills the pairs"""
import sys
from collections import Counter
from fmem import in_F, inv
from gens4 import FG, NG, ZG, words
XG = dict(NG); XG.update(ZG)
FW = words(FG, int(sys.argv[2]))
GW = words(XG, int(sys.argv[1]))
def T(g): return [(fs, f) for fs, f in FW if in_F(g + f + inv(g))]
TT = {s: (g, T(g)) for s, g in GW}
TT = {s: v for s, v in TT.items() if v[1]}
st = Counter(); ex = []
for s1, (g1i, Tq) in TT.items():
    b1 = inv(g1i)
    for s3, (b3, Tp) in TT.items():
        Q = [q for q in Tq if not in_F(b3 + q[1] + inv(b3))]
        Pp = [p for p in Tp if not in_F(g1i + p[1] + b1)]
        if not (Q and Pp): st['Q/P fail'] += 1; continue
        Tf = T(b3 + b1)
        if not Tf: st['T(b3b1) empty'] += 1; continue
        Tg = [f for f in Tf if not in_F(b1 + f[1] + g1i)]
        if not Tg: st['r in F0'] += 1; ex.append((s1, s3, [f[0] for f in Tf][:4])); continue
        st['HIT'] += 1
print(st); print(ex[:15])
