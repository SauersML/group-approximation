#!/usr/bin/python3.11
# Test T1 for Labbe's shift: for legal rho, rho' on B(r+1) that agree on their overlap at offset
# delta (|delta|_1 <= 2) but whose union is illegal, is the illegality witnessed by a union of two
# radius-r sub-balls at offset <= 2 (an interacting pair), only at offsets 3-4, or by no pair at all?
import sys, time
from collections import defaultdict
exec(open('labbe_lang.py').read().split("rmax = int")[0])
T0 = time.time()
RMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 9
def pats22(I):
    return {(I[x][y], I[x][y + 1], I[x + 1][y], I[x + 1][y + 1]) for x in range(len(I) - 1) for y in range(len(I[0]) - 1)}
big = [[0]]
for k in range(7):
    big = omega(big)
L22 = pats22(big)
while True:
    new = set(L22)
    for q in L22:
        new |= pats22(omega([[q[0], q[1]], [q[2], q[3]]]))
    if new == L22:
        break
    L22 = new
J, ms, lv = 0, 1, {a: [[a]] for a in range(19)}
while ms < 2 * RMAX + 1:
    lv = {a: omega(lv[a]) for a in range(19)}
    ms = min(min(len(lv[a]), len(lv[a][0])) for a in range(19))
    J += 1
BM = ball(RMAX)
idxM = {v: i for i, v in enumerate(BM)}
Lmax = set()
for q in L22:
    I = [[q[0], q[1]], [q[2], q[3]]]
    for _ in range(J):
        I = omega(I)
    for x in range(RMAX, len(I) - RMAX):
        for y in range(RMAX, len(I[0]) - RMAX):
            Lmax.add(tuple(I[x + a][y + b] for (a, b) in BM))
print('|L_B(%d)| = %d, level %d, time %.1f' % (RMAX, len(Lmax), J, time.time() - T0), flush=True)
cache = {}
def legal_on(shape):  # shape: sorted tuple of sites inside B(RMAX)
    if shape not in cache:
        pos = [idxM[v] for v in shape]
        cache[shape] = {tuple(p[i] for i in pos) for p in Lmax}
    return cache[shape]
def ballc(r, c):
    return [(a + c[0], b + c[1]) for (a, b) in ball(r)]
H5 = [(0, 0), (1, 0), (0, 1), (-1, 0), (0, -1)]
deltas = [(1, 0), (0, 1), (2, 0), (0, 2), (1, 1), (1, -1)]
for r1 in range(2, RMAX - 2):
    r = r1 - 1
    Lb = legal_on(tuple(sorted(ballc(r1, (0, 0)))))
    Bb = sorted(ballc(r1, (0, 0)))
    for d in deltas:
        U = tuple(sorted(set(Bb) | set(ballc(r1, d))))
        LU = legal_on(U)
        ov = [v for v in Bb if abs(v[0] - d[0]) + abs(v[1] - d[1]) <= r1]
        iv = {v: i for i, v in enumerate(Bb)}
        D = defaultdict(list)
        for q in Lb:  # q as pattern on B(r1)+d: site v has q[iv[v - d]]
            D[tuple(q[iv[(v[0] - d[0], v[1] - d[1])]] for v in ov)].append(q)
        pairs = []
        for h in H5:
            for h2 in H5:
                c2 = (d[0] + h2[0], d[1] + h2[1])
                off = abs(c2[0] - h[0]) + abs(c2[1] - h[1])
                sh = tuple(sorted(set(ballc(r, h)) | set(ballc(r, c2))))
                pairs.append((off, sh))
        pairs.sort()
        tot = illegal = w_int = w_far = w_none = 0
        for p in Lb:
            key = tuple(p[iv[v]] for v in ov)
            for q in D.get(key, ()):
                tot += 1
                u = {v: p[iv[v]] for v in Bb}
                for v in ballc(r1, d):
                    u.setdefault(v, q[iv[(v[0] - d[0], v[1] - d[1])]])
                if tuple(u[v] for v in U) in LU:
                    continue
                illegal += 1
                wit = None
                for off, sh in pairs:
                    if tuple(u[v] for v in sh) not in legal_on(sh):
                        wit = off
                        break
                if wit is None:
                    w_none += 1
                elif wit <= 2:
                    w_int += 1
                else:
                    w_far += 1
        print('B(%d) delta=%s: agreeing pairs %d, illegal unions %d, witnessed at offset<=2: %d, only at offset 3-4: %d, no pair witness: %d  time %.1f'
              % (r1, d, tot, illegal, w_int, w_far, w_none, time.time() - T0), flush=True)
print('DONE time %.1f' % (time.time() - T0))
