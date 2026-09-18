#!/usr/bin/env python3
"""Brute-force check of the path structure used in the proof, on F_2 x Z with m = 3.

For N = 3 it enumerates every excursion path and checks:
 (1) each path has pairwise distinct edges (it is a trail; it need not be self-avoiding,
     since an excursion top along t_i is a vertex of the next fibre);
 (2) the ensemble size matches 2n b^(N-1) m w'^(N-1), w' = m + (E-1) m^2 (m-1) + m (m-1)^2;
 (3) on random pairs, an edge of block i of one path equals an edge of block i' of the
     other only if i = i' <= j+1, where j is the length of the common word prefix.
"""
import random
D = {'a': [0, 1, 3], 'b': [0, 1, 4]}
LET = ['a', 'a-', 'b', 'b-']


def inv(l):
    return l[0] if len(l) == 2 else l + '-'


def mul(w, l):
    return w[:-1] if w and w[-1] == inv(l) else w + (l,)


def dec(l):
    return D[l[0]] if len(l) == 1 else [-d for d in D[l[0]]]


def paths(N):
    out = []

    def rec(i, vx, prev, word, edges, blocks):
        if i == N:
            out.append((word, edges, blocks))
            return
        for t in LET:
            if prev is not None and t == inv(prev):
                continue
            # slot (only for i >= 1) then step t
            opts = [(vx, [])]
            if i >= 1:
                for e in LET:
                    if e == inv(prev):
                        continue
                    for u in dec(e):
                        for u2 in dec(e):
                            if u == u2:
                                continue
                            y = (mul(vx[0], e), vx[1] + u)
                            plus = (vx[0], vx[1] + u - u2)
                            opts.append((plus, [frozenset((vx, y)), frozenset((y, plus))], e, u2))
            for opt in opts:
                start, exc = opt[0], opt[1]
                for s in dec(t):
                    if len(opt) > 2 and opt[2] == t and s == opt[3]:
                        continue
                    nxt = (mul(start[0], t), start[1] + s)
                    ne = exc + [frozenset((start, nxt))]
                    rec(i + 1, nxt, t, word + (t,), edges + ne, blocks + [i + 1] * len(ne))
    rec(0, ((), 0), None, (), [], [])
    return out


N = 3
P = paths(N)
m, E, n, b = 3, 3, 2, 3
wp = m + (E - 1) * m * m * (m - 1) + m * (m - 1) ** 2
assert len(P) == 2 * n * b ** (N - 1) * m * wp ** (N - 1), len(P)
for word, edges, blocks in P:
    assert len(set(edges)) == len(edges)
    assert all(len(e) == 2 for e in edges)
print('paths', len(P), 'all with pairwise distinct edges; count formula OK')
random.seed(1)
bywordprefix = {}
for idx, (word, _, _) in enumerate(P):
    bywordprefix.setdefault(word[:2], []).append(idx)
checked = shared = 0
for trial in range(400000):
    i1 = random.randrange(len(P))
    # bias towards long common prefixes
    group = bywordprefix[P[i1][0][:2]] if trial % 2 else range(len(P))
    i2 = random.choice(group)
    w1, e1, b1 = P[i1]
    w2, e2, b2 = P[i2]
    j = 0
    while j < N and w1[j] == w2[j]:
        j += 1
    pos2 = {e: k for k, e in enumerate(e2)}
    for k, e in enumerate(e1):
        if e in pos2:
            shared += 1
            assert b1[k] == b2[pos2[e]] and b1[k] <= j + 1, (w1, w2, b1[k], b2[pos2[e]], j)
    checked += 1
print('pairs checked', checked, 'shared edge incidences', shared, ': all in the same block, index <= j+1')
