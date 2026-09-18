"""Long thin tori, Z/2 dipoles with |g|_1 >> lambda_1: the two-cut strip surgery of
torus-dipole-covers-rank-distance-linear-in-profile (theory cuts: piece I1 = [r0-2l, r1+2l] around the
shorter row arc from the charge at 0 to the charge at g, I2 = complement), used when the row distance
D >= 7l; otherwise the path cut.  Checks commutation, exact ranks, exact rho, and the proof's bound
changed squares <= 12 lambda_1 + 5 (sum over b and c).
usage: python3 strips_thin.py seed"""
import sys, random
import numpy as np
from strips import S, P, frame, rows, reglue, cancel, build_pair
random.seed(int(sys.argv[1])); worst = [0, 0, 0]; cases = 0
for N1 in (1, 2, 3, 4):
    for N2 in (12, 18, 24, 36, 48):
        for C in sorted(set([0, N1 // 2, N1 - 1])):
            T = S.Torus(N1, N2, C); w, k, v, u = frame(T); lam1 = abs(w[0]) + abs(w[1]); l = max(map(abs, v))
            L, r = rows(T, v, k)
            gs = random.sample(range(1, T.N), min(6, T.N - 1))
            for g in gs:
                beta, gamma, gl = S.build(T, g)
                bp, cp = (np.array(p) for p in S.perms(T, beta, gamma))
                rho = P.profile(bp, cp)[0]
                r0, r1 = r[0], r[g]; D = (r1 - r0) % L
                if D > L // 2: r0, r1, D = r1, r0, L - D
                if D >= 7 * l:
                    cuts = sorted([(r0 - 2 * l) % L, (r1 + 2 * l + 1) % L])
                    nb, nc, pieces = reglue(T, v, u, L, r, cuts)
                    b2f, g2f = cancel(T.N, nb, nc, beta, gamma)
                    b2, c2 = build_pair(T.N, nb, nc, b2f, g2f)
                    assert np.array_equal(b2[c2], c2[b2])
                    chg = sum(1 for x in range(T.N) if (nb[x], b2f[x]) != (bp[2 * x] // 2, beta[x])) + \
                          sum(1 for x in range(T.N) if (nc[x], g2f[x]) != (cp[2 * x] // 2, gamma[x]))
                    d = max(P.rk(b2, bp), P.rk(c2, cp)); how = 'strip'
                    assert chg <= 12 * lam1 + 5, (N1, N2, C, g, chg)
                else:
                    d = gl; chg = gl; how = 'path'
                cases += 1
                worst = [max(worst[0], d / rho), max(worst[1], chg / lam1), max(worst[2], gl / rho)]
                print(N1, N2, C, g, 'lam1=%d |g|=%d D=%d l=%d' % (lam1, gl, D, l), how, 'dist<=%d changed=%d' % (d, chg),
                      'rho=%.3f' % rho, 'dist/rho=%.3f' % (d / rho), '|g|/rho=%.3f' % (gl / rho), flush=True)
print('CASES', cases, 'WORST dist/rho %.3f  changed/lambda1 %.3f  pathcut |g|/rho %.3f' % tuple(worst))
