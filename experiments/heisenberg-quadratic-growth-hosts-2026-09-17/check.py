#!/usr/bin/env python3
"""Checks for heisenberg-group-has-no-bounded-displacement-action-on-quadratic-growth-graphs.

1. Exact word lengths |c^N| in H_3(Z) = <a,b>, c = [a,b], by BFS; checks |c^N| <= 12 sqrt(N).
2. Schreier graphs X_L = H_3 / <a, b^L, c^L> on (Z/L)^2:
   b:(t,u)->(t+1,u), c:(t,u)->(t,u+1), a:(t,u)->(t,u+t).
   Prints ball sizes |B(r)| at r ~ sqrt(L). They grow like r^3, so the quadratic-growth
   box count (the step every quadratic host dies at) does not extend to cubic growth.
3. Faithfulness of the family X_L on a sample of short words.
Run: python3 check.py
"""
import math
from collections import deque

def mul(g, h):
    return (g[0] + h[0], g[1] + h[1], g[2] + h[2] + g[0] * h[1])

def inv(g):
    return (-g[0], -g[1], -g[2] + g[0] * g[1])

A, B = (1, 0, 0), (0, 1, 0)
GENS = [A, B, inv(A), inv(B)]
C = mul(mul(A, B), mul(inv(A), inv(B)))

def check_distortion(R=16):
    dist = {(0, 0, 0): 0}
    q = deque([(0, 0, 0)])
    while q:
        g = q.popleft()
        if dist[g] == R:
            continue
        for s in GENS:
            h = mul(g, s)
            if h not in dist:
                dist[h] = dist[g] + 1
                q.append(h)
    assert C in ((0, 0, 1), (0, 0, -1)), C
    worst = 0.0
    N = 1
    rows = []
    while (0, 0, N) in dist:
        l = dist[(0, 0, N)]
        worst = max(worst, l / math.sqrt(N))
        assert l <= 12 * math.sqrt(N)
        if N in (1, 4, 9, 16, 25, 36, 49, 64):
            rows.append((N, l))
        N += 1
    print("exact |c^N| (N, length):", rows, "; checked N <", N, "; max |c^N|/sqrt(N) =", round(worst, 3))

def schreier_growth(L, radii):
    def nbrs(t, u):
        yield ((t + 1) % L, u); yield ((t - 1) % L, u)
        yield (t, (u + 1) % L); yield (t, (u - 1) % L)
        yield (t, (u + t) % L); yield (t, (u - t) % L)
    d = {(0, 0): 0}
    q = deque([(0, 0)])
    rmax = max(radii)
    while q:
        v = q.popleft()
        if d[v] == rmax:
            continue
        for w in nbrs(*v):
            if w not in d:
                d[w] = d[v] + 1
                q.append(w)
    out = []
    for r in radii:
        n = sum(1 for x in d.values() if x <= r)
        out.append((r, n, round(n / r ** 2, 1), round(n / r ** 3, 2)))
    return out

def act(word, L, pt):
    t, u = pt
    for s in word:
        if s == 'a': u = (u + t) % L
        elif s == 'A': u = (u - t) % L
        elif s == 'b': t = (t + 1) % L
        elif s == 'B': t = (t - 1) % L
    return (t, u)

def faithful_sample():
    import itertools
    seen = 0
    for n in range(1, 7):
        for w in itertools.product('abAB', repeat=n):
            g = (0, 0, 0)
            for s in w:
                g = mul(g, {'a': A, 'b': B, 'A': inv(A), 'B': inv(B)}[s])
            if g == (0, 0, 0):
                continue
            ok = any(act(w, L, (t, u)) != (t, u) for L in range(2, 30) for t in range(L) for u in (0,))
            assert ok, w
            seen += 1
    print("nontrivial words of length <= 6 all act nontrivially on some X_L, L < 30:", seen)

if __name__ == "__main__":
    check_distortion()
    L = 4096
    print("X_L growth, L =", L, "(r, |B(r)|, |B|/r^2, |B|/r^3):", schreier_growth(L, [8, 16, 32, 64]))
    faithful_sample()
