"""Conjugators n in P_X that transport a two-letter F-element u^e v^d (u != v meridians) into F
while transporting neither u nor v:  n w n^-1 in F  but  n u n^-1, n v n^-1 not in F.
These are the 'pair twists' a flower hexagon needs on its third petal.
Run: python3 pairtr.py LG [K r]   (chunked over the word list)"""
import sys
from fmem import in_F, inv
from gens4 import FG, NG, ZG, words

LG = int(sys.argv[1]); K = int(sys.argv[2]) if len(sys.argv) > 2 else 1; r = int(sys.argv[3]) if len(sys.argv) > 3 else 0
XG = dict(NG); XG.update(ZG)
names = sorted(FG)
cands = []
for i, u in enumerate(names):
    for v in names:
        if u == v:
            continue
        for e in (1, -1):
            for d in (1, -1):
                w = (FG[u] if e == 1 else inv(FG[u])) + (FG[v] if d == 1 else inv(FG[v]))
                cands.append(('%s%s %s%s' % (u, "'" if e < 0 else '', v, "'" if d < 0 else ''), u, v, w))
n_tot = 0
for idx, (s, g) in enumerate(words(XG, LG)):
    if idx % K != r:
        continue
    n_tot += 1
    single = {u: in_F(g + FG[u] + inv(g)) for u in names}
    for cs, u, v, w in cands:
        if single[u] or single[v]:
            continue
        if in_F(g + w + inv(g)):
            print('PAIR n=[%s] transports [%s]; singles %s' % (s, cs, single), flush=True)
print('done', n_tot)
