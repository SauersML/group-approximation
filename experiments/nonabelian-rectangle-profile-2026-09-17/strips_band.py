"""The exact construction of torus-dipole-covers-rank-distance-linear-in-profile-proof, checked step by step.

Z/2 dipole (charges at vertices 0 and g, surgery.build).  Row distance D between the charges.
If D <= 2l: path cut, cost |g|_1; check |g|_1 <= sqrt2 (D/|v|_2 + |w|_2/2) (Lemma 1).
If D >= 2l+1: pieces I1 = [r0, r1] (height D+1) and I2 = complement; reglue (Lemma 2); check
  (a) #redirected base points (b and c counted separately) <= 2 lambda_1,
  (b) new charge support is inside R u {0, g},
  (c) every charged vertex has loc in [0,l) u [H-l,H)  (the seam zone),
  (d) the band loc in [H-l, H-l+|v|_1) mod H has exactly lambda_1 vertices and is connected (Lemma 3),
  (e) every charged vertex lies in the band or is one grid step from it,
then cancel along a BFS spanning tree of (band u charged) in each piece, count changed sites,
check <= 6 lambda_1, check commutation and exact ranks, and compare with exact rho.
usage: python3 strips_band.py exh Nmin Nmax | thin seed
"""
import sys, random
from math import sqrt
from collections import deque
import numpy as np
from strips import S, P, frame, rows, reglue, build_pair

def construct(T, g, v, u, k, L, r, lam1, l):
    beta, gamma, gl = S.build(T, g); N = T.N
    bp, cp = (np.array(p) for p in S.perms(T, beta, gamma))
    r0, r1 = r[0], r[g]; D = (r1 - r0) % L
    if D > L // 2: r0, r1, D = r1, r0, L - D
    if D <= 2 * l:
        w2 = sqrt((k * v[0]) ** 2 + (k * v[1]) ** 2)
        assert gl <= sqrt(2) * (D / sqrt(v[0] ** 2 + v[1] ** 2) + w2 / 2) + 1e-9
        return 'path', gl, gl, D, bp, cp
    nb, nc, pieces = reglue(T, v, u, L, r, [r0, (r1 + 1) % L])
    b0 = [bp[2 * x] // 2 for x in range(N)]; c0 = [cp[2 * x] // 2 for x in range(N)]
    Rb = {x for x in range(N) if nb[x] != b0[x]}; Rc = {x for x in range(N) if nc[x] != c0[x]}
    assert len(Rb) + len(Rc) <= 2 * lam1                                   # (a)
    kap = lambda x, be, ga: be[x] ^ ga[nb[x]] ^ ga[x] ^ be[nc[x]]
    Q = {x for x in range(N) if kap(x, beta, gamma)}
    assert Q <= (Rb | Rc | {0, g})                                          # (b)
    ib = [0] * N; ic = [0] * N
    for h in range(N): ib[nb[h]] = h; ic[nc[h]] = h
    adj = [[] for _ in range(N)]
    for x in range(N):
        adj[x] += [(ic[x], 'b', x), (ib[x], 'g', x)]; adj[ic[x]].append((x, 'b', x)); adj[ib[x]].append((x, 'g', x))
    be, ga = beta[:], gamma[:]; changes = 0; v1n = abs(v[0]) + abs(v[1])
    for j, (s, H) in enumerate(pieces):
        loc = {x: (r[x] - s) % L for x in range(N) if (r[x] - s) % L < H}
        Qj = {x for x in Q if x in loc}
        assert all(loc[x] < l or loc[x] >= H - l for x in Qj)              # (c)
        band = {x for x in loc if (loc[x] - (H - l)) % H < v1n}
        assert len(band) == lam1                                            # (d)
        V = band | Qj
        for x in Qj:                                                        # (e)
            assert x in band or any(y in band for (y, _, _) in adj[x])
        root = min(band); par = {root: None}; order = [root]; dq = deque([root])
        while dq:
            x = dq.popleft()
            for (y, lab, e) in adj[x]:
                if y in V and y not in par: par[y] = (x, lab, e); order.append(y); dq.append(y)
        assert set(par) == V and set(order) >= band                         # connected
        val = {x: (1 if x in Qj else 0) for x in V}
        for y in reversed(order[1:]):
            if val[y]:
                x, lab, e = par[y]
                if lab == 'b': be[e] ^= 1
                else: ga[e] ^= 1
                val[y] = 0; val[x] ^= 1; changes += 1
        assert val[root] == 0 and len(V) - 1 <= lam1 - 1 + len(Qj - band)
    assert all(kap(x, be, ga) == 0 for x in range(N))
    b2, c2 = build_pair(N, nb, nc, be, ga)
    assert np.array_equal(b2[c2], c2[b2])
    chg = sum(1 for x in range(N) if (nb[x], be[x]) != (b0[x], beta[x])) + \
          sum(1 for x in range(N) if (nc[x], ga[x]) != (c0[x], gamma[x]))
    assert chg <= len(Rb) + len(Rc) + changes and chg <= 6 * lam1, (chg, lam1)
    return 'strip', max(P.rk(b2, bp), P.rk(c2, cp)), chg, D, bp, cp

def run(cases_iter):
    worst = [0.0, 0.0]; n = 0; ns = 0
    for T, g in cases_iter:
        w, k, v, u = frame(T); lam1 = abs(w[0]) + abs(w[1]); l = max(map(abs, v)); L, r = rows(T, v, k)
        how, d, chg, D, bp, cp = construct(T, g, v, u, k, L, r, lam1, l)
        rho = P.profile(bp, cp)[0]; n += 1; ns += how == 'strip'
        worst = [max(worst[0], d / rho), max(worst[1], chg / lam1 if how == 'strip' else 0)]
        print(T.N1, T.N2, T.C, g, 'lam1=%d D=%d l=%d' % (lam1, D, l), how, 'dist<=%d changed=%d rho=%.3f ratio=%.3f'
              % (d, chg, rho, d / rho), flush=True)
    print('CASES', n, 'STRIP', ns, 'WORST dist/rho %.3f  strip changed/lambda1 %.3f' % tuple(worst))

if __name__ == "__main__":
    if sys.argv[1] == 'exh':
        a, b = int(sys.argv[2]), int(sys.argv[3])
        run((S.Torus(N1, N // N1, C), g) for N in range(a, b + 1) for N1 in range(1, N + 1) if N % N1 == 0
            for C in range(N1) for g in range(1, N))
    else:
        random.seed(int(sys.argv[2]))
        def gen():
            for N1 in (1, 2, 3, 4):
                for N2 in (12, 18, 24, 36, 48):
                    for C in sorted(set([0, N1 // 2, N1 - 1])):
                        T = S.Torus(N1, N2, C)
                        for g in random.sample(range(1, T.N), min(6, T.N - 1)): yield T, g
        run(gen())
