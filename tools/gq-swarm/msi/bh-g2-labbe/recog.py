#!/usr/bin/env python3
# Local recognizability radius of omega^2 (and omega) on Labbe's Wang shift Omega_U.
# Tile data and alpha, beta, gamma copied verbatim from experiments/fp-simple-relation-climbing/labbe_lang.py
# (arXiv:1802.03265). Single-threaded, stdlib only, no randomness.
#
# For R = 0, 1, 2, ...: every legal (2R+1)x(2R+1) window of Omega_U occurs in omega^k(q) for a legal 2x2 pattern q,
# where min width/height of omega^k images >= 2R (then a window meets at most two omega^k blocks per direction).
# Write omega^k = omega^m o omega^(k-m) (m = 2 or 1): the omega^m-parse of the window centre (block corner with parent
# letter a, or not a corner) is read off the layout of omega^m(omega^(k-m)(q)); by recognizability (Labbe) this is the
# parse in every tiling. R is "local" iff no window pattern gets two different parses.
import sys, time
T0 = time.time()
tilesU = ['FOJO','FOHL','JMFP','DMFK','HPJP','HPHN','HKFP','HKDP','BOIO','GLEO','GLCL','ALIO',
          'EPGP','EPIP','IPGK','IPIK','IKBM','IKAK','CNIP']
alpha = {0: [[11]], 1: [[8]], 2: [[13]], 3: [[9]], 4: [[17]], 5: [[16]], 6: [[14]], 7: [[15]], 8: [[11, 1]], 9: [[8, 0]], 10: [[18, 5]], 11: [[12, 6]], 12: [[13, 7]], 13: [[13, 4]], 14: [[10, 1]], 15: [[9, 1]], 16: [[17, 3]], 17: [[16, 3]], 18: [[14, 6]], 19: [[15, 7]], 20: [[14, 2]]}
beta = {0: [[4]], 1: [[5]], 2: [[7], [0]], 3: [[4], [1]], 4: [[5], [1]], 5: [[6], [1]], 6: [[7], [1]], 7: [[2], [3]], 8: [[16]], 9: [[17]], 10: [[18]], 11: [[20]], 12: [[18], [8]], 13: [[19], [8]], 14: [[20], [9]], 15: [[11], [15]], 16: [[12], [15]], 17: [[10], [14]], 18: [[13], [15]]}
gamma = {0: [[0]], 1: [[1]], 2: [[2]], 3: [[7]], 4: [[3]], 5: [[4]], 6: [[6]], 7: [[5]], 8: [[10]], 9: [[8]], 10: [[9]], 11: [[11]], 12: [[13]], 13: [[12]], 14: [[16]], 15: [[15]], 16: [[17]], 17: [[18]], 18: [[14]]}
ci = {c: i for i, c in enumerate('RTLB')}
RT = [t[ci['R']] for t in tilesU]; TP = [t[ci['T']] for t in tilesU]
LF = [t[ci['L']] for t in tilesU]; BT = [t[ci['B']] for t in tilesU]

def apply(s, M):  # M: list of columns, each bottom -> top (same convention as labbe_lang.py)
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

def omega_pow(M, k):
    for _ in range(k):
        M = omega(M)
    return M

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

# Legal 2x2 patterns, exactly as in labbe_lang.py: 2x2 factors of omega^7(0), closed under omega.
big = omega_pow([[0]], 7)
L22 = set()
def add22(I, S):
    for x in range(len(I) - 1):
        for y in range(len(I[0]) - 1):
            S.add((I[x][y], I[x][y + 1], I[x + 1][y], I[x + 1][y + 1]))
add22(big, L22)
while True:
    new = set(L22)
    for q in L22:
        add22(omega([[q[0], q[1]], [q[2], q[3]]]), new)
    if new == L22:
        break
    L22 = new
Q2 = sorted(L22)
print('|L_2x2| =', len(Q2), 'all Wang-valid:', all(valid([[q[0], q[1]], [q[2], q[3]]]) for q in Q2), flush=True)

# Shapes of omega^k images (min over letters of width and of height).
minw = {}
for k in range(1, 9):
    imgs = [omega_pow([[a]], k) for a in range(19)]
    minw[k] = min(min(len(I) for I in imgs), min(len(I[0]) for I in imgs))
print('min side of omega^k(a):', minw, flush=True)

def layout(X, m):
    """omega^m(X) with its omega^m block structure: returns (Y, C) with C[x][y] = parent letter if (x,y) is the
    lower-left corner of a block, else -1. Asserts column-constant widths, row-constant heights, and Y = omega^m(X)."""
    img = {a: omega_pow([[a]], m) for a in range(19)}
    cw = [len(img[X[c][0]]) for c in range(len(X))]
    rh = [len(img[X[0][r]][0]) for r in range(len(X[0]))]
    for c in range(len(X)):
        for r in range(len(X[0])):
            a = X[c][r]
            assert len(img[a]) == cw[c] and len(img[a][0]) == rh[r], 'shape inconsistency'
    W, H = sum(cw), sum(rh)
    Y = [[None] * H for _ in range(W)]
    C = [[-1] * H for _ in range(W)]
    x0 = 0
    for c in range(len(X)):
        y0 = 0
        for r in range(len(X[0])):
            B = img[X[c][r]]
            for i in range(cw[c]):
                for j in range(rh[r]):
                    Y[x0 + i][y0 + j] = B[i][j]
            C[x0][y0] = X[c][r]
            y0 += rh[r]
        x0 += cw[c]
    assert Y == omega_pow(X, m), 'layout differs from omega^m'
    return Y, C

def radius(m, Rmax):
    res = {}
    cache = {}
    for R in range(0, Rmax + 1):
        k = next(k for k in range(m, 9) if minw[k] >= 2 * R)
        if k not in cache:
            cache[k] = []
            for q in Q2:
                X = omega_pow([[q[0], q[1]], [q[2], q[3]]], k - m)
                Y, C = layout(X, m)
                assert valid(Y)
                cache[k].append((Y, C))
        seen = {}
        conflicts = 0
        example = None
        for Y, C in cache[k]:
            W, H = len(Y), len(Y[0])
            for x in range(R, W - R):
                cols = Y[x - R:x + R + 1]
                for y in range(R, H - R):
                    key = tuple(tuple(col[y - R:y + R + 1]) for col in cols)
                    v = C[x][y]
                    old = seen.get(key)
                    if old is None:
                        seen[key] = v
                    elif old != v:
                        conflicts += 1
                        if example is None:
                            example = (key, old, v)
        print('omega^%d  R=%d  k=%d  distinct windows=%d  conflicts=%d  (%.1fs)'
              % (m, R, k, len(seen), conflicts, time.time() - T0), flush=True)
        if conflicts and example:
            print('   example window (columns bottom->top):', example[0], 'parses', example[1], example[2], flush=True)
        res[R] = conflicts
        if conflicts == 0:
            break
    return res

Rmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
r2 = radius(2, Rmax)
r1 = radius(1, Rmax)
print('RESULT omega^2:', r2)
print('RESULT omega:', r1)
print('total %.1fs' % (time.time() - T0))
