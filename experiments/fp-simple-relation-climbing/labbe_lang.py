#!/usr/bin/python3.11
# Exact language of Labbe's Wang shift Omega_U (arXiv:1802.03265) from omega = alpha*beta*gamma,
# the ChJN incompatibility radius R_1, and "hidden illegal" B(r+1)-patterns: all five
# restrictions to B(r)+h (|h|_1 <= 1) legal, pattern itself illegal.
import sys, time
from collections import defaultdict
T0 = time.time()
tilesU = ['FOJO','FOHL','JMFP','DMFK','HPJP','HPHN','HKFP','HKDP','BOIO','GLEO','GLCL','ALIO',
          'EPGP','EPIP','IPGK','IPIK','IKBM','IKAK','CNIP']
alpha = {0: [[11]], 1: [[8]], 2: [[13]], 3: [[9]], 4: [[17]], 5: [[16]], 6: [[14]], 7: [[15]], 8: [[11, 1]], 9: [[8, 0]], 10: [[18, 5]], 11: [[12, 6]], 12: [[13, 7]], 13: [[13, 4]], 14: [[10, 1]], 15: [[9, 1]], 16: [[17, 3]], 17: [[16, 3]], 18: [[14, 6]], 19: [[15, 7]], 20: [[14, 2]]}
beta = {0: [[4]], 1: [[5]], 2: [[7], [0]], 3: [[4], [1]], 4: [[5], [1]], 5: [[6], [1]], 6: [[7], [1]], 7: [[2], [3]], 8: [[16]], 9: [[17]], 10: [[18]], 11: [[20]], 12: [[18], [8]], 13: [[19], [8]], 14: [[20], [9]], 15: [[11], [15]], 16: [[12], [15]], 17: [[10], [14]], 18: [[13], [15]]}
gamma = {0: [[0]], 1: [[1]], 2: [[2]], 3: [[7]], 4: [[3]], 5: [[4]], 6: [[6]], 7: [[5]], 8: [[10]], 9: [[8]], 10: [[9]], 11: [[11]], 12: [[13]], 13: [[12]], 14: [[16]], 15: [[15]], 16: [[17]], 17: [[18]], 18: [[14]]}
CONV = sys.argv[2] if len(sys.argv) > 2 else 'RTLB'
ci = {c: i for i, c in enumerate(CONV)}
RT = [t[ci['R']] for t in tilesU]; TP = [t[ci['T']] for t in tilesU]
LF = [t[ci['L']] for t in tilesU]; BT = [t[ci['B']] for t in tilesU]

def apply(s, M):  # M: list of columns, each bottom -> top
    out = []
    for col in M:
        imgs = [s[a] for a in col]
        w = len(imgs[0])
        if any(len(im) != w for im in imgs):
            raise ValueError('width')
        for j in range(w):
            c = []
            for im in imgs:
                c.extend(im[j])
            out.append(c)
    if any(len(c) != len(out[0]) for c in out):
        raise ValueError('height')
    return out

def omega(M):
    return apply(alpha, apply(beta, apply(gamma, M)))

def valid(M):
    W, H = len(M), len(M[0])
    for x in range(W):
        for y in range(H):
            t = M[x][y]
            if x + 1 < W and RT[t] != LF[M[x + 1][y]]:
                return False
            if y + 1 < H and TP[t] != BT[M[x][y + 1]]:
                return False
    return True

def ball(r):
    return sorted((a, b) for a in range(-r, r + 1) for b in range(-r, r + 1) if abs(a) + abs(b) <= r)

rmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
M = [[0]]
for k in range(1, 5):
    M = omega(M)
    print('omega^%d(0) dims %dx%d valid %s' % (k, len(M), len(M[0]), valid(M)), flush=True)
big = [[0]]
for k in range(7):
    big = omega(big)
print('omega^7(0) dims %dx%d valid %s' % (len(big), len(big[0]), valid(big)), flush=True)
L22 = set()
def add22(I, S):
    for x in range(len(I) - 1):
        for y in range(len(I[0]) - 1):
            S.add((I[x][y], I[x][y + 1], I[x + 1][y], I[x + 1][y + 1]))
add22(big, L22)
while True:
    new = set(L22)
    for q in L22:
        I = omega([[q[0], q[1]], [q[2], q[3]]])
        if not valid(I):
            print('INVALID image of 2x2', q)
        add22(I, new)
    if new == L22:
        break
    L22 = new
print('|L_2x2| =', len(L22), 'all valid:', all(valid([[q[0], q[1]], [q[2], q[3]]]) for q in L22), flush=True)
lvl = {a: [[a]] for a in range(19)}
minsize = [1]
J = 0
while minsize[-1] < 2 * rmax + 1:
    lvl = {a: omega(lvl[a]) for a in range(19)}
    minsize.append(min(min(len(lvl[a]), len(lvl[a][0])) for a in range(19)))
J = len(minsize) - 1
print('min supertile side by level', minsize, 'using level', J, flush=True)
Bs = {r: ball(r) for r in range(rmax + 1)}
idx = {r: {v: i for i, v in enumerate(Bs[r])} for r in Bs}
Lmax = set()
npos = 0
for q in L22:
    I = [[q[0], q[1]], [q[2], q[3]]]
    for _ in range(J):
        I = omega(I)
    W, H = len(I), len(I[0])
    for x in range(rmax, W - rmax):
        for y in range(rmax, H - rmax):
            Lmax.add(tuple(I[x + a][y + b] for (a, b) in Bs[rmax]))
            npos += 1
Lr = {rmax: Lmax}
for r in range(rmax - 1, -1, -1):
    pos = [idx[r + 1][v] for v in Bs[r]]
    Lr[r] = {tuple(p[i] for i in pos) for p in Lr[r + 1]}
print('positions', npos, 'time %.1f' % (time.time() - T0))
print('|L_B(r)| for r=0..%d:' % rmax, [len(Lr[r]) for r in range(rmax + 1)], flush=True)
for R in range(0, rmax - 2):
    gs = [(a, b) for a in range(-3, 4) for b in range(-3, 4) if 0 < abs(a) + abs(b) <= 3]
    pos0 = [idx[R + 3][v] for v in Bs[R]]
    bad = []
    for g in gs:
        posg = [idx[R + 3][(v[0] + g[0], v[1] + g[1])] for v in Bs[R]]
        if any(all(p[i] == p[j] for i, j in zip(pos0, posg)) for p in Lr[R + 3]):
            bad.append(g)
    print('R=%d: translates |g|<=3 compatible with some legal B(R) patch: %s' % (R, bad), flush=True)
dirs = [(1, 0), (0, 1), (-1, 0), (0, -1)]
for r in range(1, rmax):
    B = Bs[r]
    S1 = [v for v in Bs[r + 1] if abs(v[0]) + abs(v[1]) == r + 1]
    ext = {}
    for h in dirs:
        Oh = [v for v in B if abs(v[0] - h[0]) + abs(v[1] - h[1]) <= r]
        Sh = [v for v in S1 if abs(v[0] - h[0]) + abs(v[1] - h[1]) <= r]
        oi = [idx[r][(v[0] - h[0], v[1] - h[1])] for v in Oh]
        si = [idx[r][(v[0] - h[0], v[1] - h[1])] for v in Sh]
        D = defaultdict(set)
        for q in Lr[r]:
            D[tuple(q[i] for i in oi)].add(tuple(q[i] for i in si))
        ext[h] = (Oh, Sh, D)
    count = legal = 0
    examples = []
    for c in Lr[r]:
        partial = [{}]
        for h in dirs:
            Oh, Sh, D = ext[h]
            opts = D.get(tuple(c[idx[r][v]] for v in Oh), ())
            newp = []
            for pd in partial:
                for o in opts:
                    if all(pd.get(v, t) == t for v, t in zip(Sh, o)):
                        nd = dict(pd)
                        nd.update(zip(Sh, o))
                        newp.append(nd)
            partial = newp
            if not partial:
                break
        for pd in partial:
            p = tuple(c[idx[r][v]] if v in idx[r] else pd[v] for v in Bs[r + 1])
            count += 1
            if p in Lr[r + 1]:
                legal += 1
            elif len(examples) < 2:
                examples.append(p)
    print('B(%d): |M| = %d  |L| = %d  legal-in-M = %d  hidden-illegal = %d  time %.1f' %
          (r + 1, count, len(Lr[r + 1]), legal, count - legal, time.time() - T0), flush=True)
    for p in examples:
        d = dict(zip(Bs[r + 1], p))
        rows = []
        for b in range(r + 1, -r - 2, -1):
            rows.append(' '.join('%2d' % d[(a, b)] if (a, b) in d else ' .' for a in range(-r - 1, r + 2)))
        print('  example hidden-illegal on B(%d):\n' % (r + 1) + '\n'.join('   ' + s for s in rows))
print('DONE time %.1f' % (time.time() - T0))
