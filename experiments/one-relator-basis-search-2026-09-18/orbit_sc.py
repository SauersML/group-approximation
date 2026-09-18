"""Search the Aut(F_2)-orbit of w (cyclic words up to length LMAX, via elementary Nielsen moves)
for a relator satisfying C'(1/6).  Usage: orbit_sc.py LMAX FILE"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import basis_search as BS, smallcanc as SC
from collections import deque
LMAX = int(sys.argv[1])
for line in open(sys.argv[2]):
    f = line.split()
    if not f: continue
    w0 = f[0]
    st = BS.canon([BS.CH[c] for c in w0]); seen = {st}; Q = deque([st]); hit = None; best = None
    while Q:
        w = Q.popleft(); s = BS.ws(w)
        L, mp, t4, wit = SC.analyse(s)
        r = mp / L
        if best is None or r < best[0]: best = (r, s, mp)
        if 6 * mp < L: hit = s; break
        for img in BS.nielsen():
            v = BS.canon(BS.subst(w, img))
            if len(v) <= LMAX and v not in seen: seen.add(v); Q.append(v)
    print('ORBIT %s states=%d -> %s best=%s(%d/%d)' % (w0, len(seen), 'C6 ' + hit if hit else 'none', best[1], best[2], len(best[1])), flush=True)
print('SENTINEL_DONE')
