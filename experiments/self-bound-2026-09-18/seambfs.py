"""Exact test: can ANY same-word loop pair at the cone point of the bi-infinite seam surface lower the excess?

Sigma_inf(a,b,c,tw): the one-cylinder H(2) surface with the height sent to infinity (one seam, two half-infinite
cylinders).  A same-word pair of paths from A keeps equal heights, and inside a half-cylinder Q is P translated by
a fixed number of columns, so every excursion into a half-cylinder can be replaced by one at depth 1 with the same
seam entry/exit edges (corner data at A unchanged).  Hence the set of reachable end data (a_P, a_Q, g_P, g_Q) over
all lengths equals the set reachable inside the band of vertex levels -1, 0, 1, which the surface onecyl(a,b,c,4,tw)
realises without wrapping (levels 3, 0, 1).  We BFS over joint states (state_P, state_Q), ignoring the admissibility
conditions (edge- and vertex-distinctness), so the reachable set is a superset.  The excess change is read off the
validated corner rule of corner.py: A's corners after the swap are the cycles of (a_P a_Q) o nu o (g_P g_Q).
"""
import sys
from collections import deque
from swap import Surf, excess
from h2 import onecyl
from corner import nu_map, cycles_on

def level(S, st, n, H):
    x, k = st; j = (k + 1) & 3
    return (x // n + (1 if j in (2, 3) else 0)) % H

def seam_data(a, b, c, tw):
    n = a + b + c; H = 4
    bb, cc = onecyl(a, b, c, H, tw); S = Surf(bb, cc)
    cones = S.cones()
    if len(cones) != 1 or len(S.cls[cones[0]]) != 12: return None
    A = cones[0]; dom = S.cls[A]; nu = nu_map(bb, cc)
    ok_lv = {3, 0, 1}
    secs = [(i // 4, i % 4) for i in dom]
    ends = {}  # (aP,aQ,gP,gQ) -> new excess at A
    for k in range(4):
        sk = [s for s in secs if s[1] == k]
        for s1 in sk:
            for s2 in sk:
                if s1 == s2: continue
                aP, aQ = 4*s1[0]+s1[1], 4*s2[0]+s2[1]
                seen = {(s1, s2)}; dq = deque([(s1, s2)])
                while dq:
                    p, q = dq.popleft()
                    vp, vq = S.vend(p), S.vend(q)
                    if vp == A or vq == A:
                        if vp == A and vq == A:
                            gP, gQ = 4*p[0] + ((p[1]+1) & 3), 4*q[0] + ((q[1]+1) & 3)
                            if gP != gQ:
                                t = {aP: aQ, aQ: aP}; u = {gP: gQ, gQ: gP}
                                perm = {x: t.get(nu[u.get(x, x)], nu[u.get(x, x)]) for x in dom}
                                cyc = cycles_on(perm, dom)
                                ends[(aP, aQ, gP, gQ)] = sum(len(z)//4 - 1 for z in cyc)
                        continue
                    for mv in (0, 1, 2):
                        p2, q2 = S.step(p, mv), S.step(q, mv)
                        if level(S, p2, n, H) not in ok_lv: continue
                        if (p2, q2) not in seen:
                            seen.add((p2, q2)); dq.append((p2, q2))
    return ends

if __name__ == '__main__':
    nmax = int(sys.argv[1])
    for n in range(3, nmax + 1):
        for a in range(1, n):
            for b in range(1, n - a):
                c = n - a - b
                for tw in range(n):
                    e = seam_data(a, b, c, tw)
                    if e is None: continue
                    low = sum(1 for v in e.values() if v == 0)
                    distinct = len({a, b, c}) == 3
                    print(n, (a, b, c), tw, 'distinct' if distinct else 'repeat', 'ends', len(e), 'lowering', low, flush=True)
