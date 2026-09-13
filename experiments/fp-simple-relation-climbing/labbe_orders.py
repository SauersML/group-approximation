#!/usr/bin/python3.11
# Order of hidden illegality for Labbe's shift: for p on B(r+1) with all five B(r)+h restrictions
# legal but p illegal, the least k such that the restriction of p to a union of k of the five balls
# is illegal. Also re-derives |L_2x2| from omega^9(0) as a completeness check.
import sys, time, itertools
from collections import defaultdict
exec(open('labbe_lang.py').read().split("rmax = int")[0])  # tiles, substitutions, apply, omega, valid, ball
T0 = time.time()
rmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
def pats22(I):
    return {(I[x][y], I[x][y + 1], I[x + 1][y], I[x + 1][y + 1]) for x in range(len(I) - 1) for y in range(len(I[0]) - 1)}
big = [[0]]
for k in range(9):
    big = omega(big)
seed = pats22(big)
print('omega^9(0) %dx%d valid %s, 2x2 patterns in it: %d' % (len(big), len(big[0]), valid(big), len(seed)), flush=True)
L22 = set(seed)
while True:
    new = set(L22)
    for q in L22:
        new |= pats22(omega([[q[0], q[1]], [q[2], q[3]]]))
    if new == L22:
        break
    L22 = new
print('|L_2x2| after closure:', len(L22), flush=True)
J, ms, lv = 0, 1, {a: [[a]] for a in range(19)}
while ms < 2 * rmax + 1:
    lv = {a: omega(lv[a]) for a in range(19)}
    ms = min(min(len(lv[a]), len(lv[a][0])) for a in range(19))
    J += 1
Bs = {r: ball(r) for r in range(rmax + 1)}
idx = {r: {v: i for i, v in enumerate(Bs[r])} for r in Bs}
Lmax = set()
for q in L22:
    I = [[q[0], q[1]], [q[2], q[3]]]
    for _ in range(J):
        I = omega(I)
    for x in range(rmax, len(I) - rmax):
        for y in range(rmax, len(I[0]) - rmax):
            Lmax.add(tuple(I[x + a][y + b] for (a, b) in Bs[rmax]))
Lr = {rmax: Lmax}
for r in range(rmax - 1, -1, -1):
    pos = [idx[r + 1][v] for v in Bs[r]]
    Lr[r] = {tuple(p[i] for i in pos) for p in Lr[r + 1]}
print('|L_B(r)|:', [len(Lr[r]) for r in range(rmax + 1)], 'time %.1f' % (time.time() - T0), flush=True)
H5 = [(0, 0), (1, 0), (0, 1), (-1, 0), (0, -1)]
for r in range(1, rmax):
    shapes = {}
    for k in range(1, 6):
        for T in itertools.combinations(range(5), k):
            U = sorted({v for t in T for v in Bs[r + 1] if abs(v[0] - H5[t][0]) + abs(v[1] - H5[t][1]) <= r})
            pos = [idx[r + 1][v] for v in U]
            shapes[T] = (pos, {tuple(p[i] for i in pos) for p in Lr[r + 1]})
    # candidates: all patterns on B(r+1) whose five sub-balls are legal (join over sphere sites)
    S1 = [v for v in Bs[r + 1] if abs(v[0]) + abs(v[1]) == r + 1]
    ext = {}
    for h in H5[1:]:
        Oh = [v for v in Bs[r] if abs(v[0] - h[0]) + abs(v[1] - h[1]) <= r]
        Sh = [v for v in S1 if abs(v[0] - h[0]) + abs(v[1] - h[1]) <= r]
        oi = [idx[r][(v[0] - h[0], v[1] - h[1])] for v in Oh]
        si = [idx[r][(v[0] - h[0], v[1] - h[1])] for v in Sh]
        D = defaultdict(set)
        for q in Lr[r]:
            D[tuple(q[i] for i in oi)].add(tuple(q[i] for i in si))
        ext[h] = (Oh, Sh, D)
    orders = defaultdict(int)
    witnesses = defaultdict(set)
    for c in Lr[r]:
        partial = [{}]
        for h in H5[1:]:
            Oh, Sh, D = ext[h]
            opts = D.get(tuple(c[idx[r][v]] for v in Oh), ())
            partial = [dict(pd, **{}) | dict(zip(Sh, o)) for pd in partial for o in opts
                       if all(pd.get(v, t) == t for v, t in zip(Sh, o))]
            if not partial:
                break
        for pd in partial:
            p = tuple(c[idx[r][v]] if v in idx[r] else pd[v] for v in Bs[r + 1])
            if p in Lr[r + 1]:
                continue
            for k in range(2, 6):
                bad = [T for T in itertools.combinations(range(5), k)
                       if tuple(p[i] for i in shapes[T][0]) not in shapes[T][1]]
                if bad:
                    orders[k] += 1
                    for T in bad:
                        witnesses[k].add(T)
                    break
    print('B(%d) hidden-illegal by order: %s; minimal illegal unions at that order: %s' %
          (r + 1, dict(sorted(orders.items())), {k: sorted(witnesses[k])[:6] for k in witnesses}), flush=True)
print('DONE time %.1f' % (time.time() - T0))
