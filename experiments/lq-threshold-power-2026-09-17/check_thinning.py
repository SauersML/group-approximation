#!/usr/bin/env python3
"""Checks for fpbs-lq-threshold-power-monotonicity.

1. The two-point convexity inequality used in the induction step:
      p^g + (1 - p^g) x^g >= (p + (1 - p) x)^g   for p, x, g in [0,1].
2. The thinning inequality P_{p^g}(A) >= P_p(A)^g on random increasing
   events of up to 6 edges (exact enumeration) and on two-terminal
   connection events of small graphs.
3. Tree calibration: on T_d, p_q = (d-1)^(-1/q) = p_c^(1/q), so
   q -> p_q^q is constant (equality in the monotonicity).
Exit code 0 iff every check passes.
"""
import random
import sys

random.seed(20260917)
grid = [i / 40 for i in range(41)]
bad = 0

# 1. two-point inequality
for p in grid:
    for x in grid:
        for g in grid[1:]:
            lhs = p**g + (1 - p**g) * x**g
            rhs = (p + (1 - p) * x) ** g
            if lhs < rhs - 1e-12:
                bad += 1
print("two-point inequality violations:", bad)


def prob(up, n, p):
    s = 0.0
    for w in range(1 << n):
        if up[w]:
            k = bin(w).count("1")
            s += p**k * (1 - p) ** (n - k)
    return s


def random_upset(n):
    gens = [random.randrange(1 << n) for _ in range(random.randint(1, 4))]
    return [any((w & m) == m for m in gens) for w in range(1 << n)]


viol = 0
for trial in range(400):
    n = random.randint(1, 6)
    up = random_upset(n)
    for p in grid[1:-1]:
        for g in (0.1, 0.3, 0.5, 0.7, 0.9):
            if prob(up, n, p**g) < prob(up, n, p) ** g - 1e-12:
                viol += 1
print("random increasing-event thinning violations:", viol)


def conn_upset(edges, nv, s, t):
    n = len(edges)
    up = []
    for w in range(1 << n):
        adj = {v: [] for v in range(nv)}
        for i, (a, b) in enumerate(edges):
            if w >> i & 1:
                adj[a].append(b)
                adj[b].append(a)
        seen, st = {s}, [s]
        while st:
            v = st.pop()
            for u in adj[v]:
                if u not in seen:
                    seen.add(u)
                    st.append(u)
        up.append(t in seen)
    return up


graphs = {
    "K4": ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], 4, 0, 3),
    "ladder2x3": ([(0, 1), (1, 2), (3, 4), (4, 5), (0, 3), (1, 4), (2, 5)], 6, 0, 5),
    "theta": ([(0, 1), (1, 4), (0, 2), (2, 4), (0, 3), (3, 4), (1, 2)], 5, 0, 4),
}
cviol = 0
for name, (E, nv, s, t) in graphs.items():
    up = conn_upset(E, nv, s, t)
    for p in grid[1:-1]:
        for g in (0.2, 0.5, 0.8):
            if prob(up, len(E), p**g) < prob(up, len(E), p) ** g - 1e-12:
                cviol += 1
print("connection-event thinning violations:", cviol)

# 3. tree calibration: Z_q(p) < inf iff (d-1) p^q < 1
tviol = 0
for d in (3, 4, 6, 10):
    pc = 1 / (d - 1)
    for q in (1, 1.5, 2, 3, 7.5):
        pq = (d - 1) ** (-1 / q)
        if abs(pq - pc ** (1 / q)) > 1e-12:
            tviol += 1
print("tree calibration mismatches:", tviol)

ok = bad == 0 and viol == 0 and cviol == 0 and tviol == 0
print("ALL OK" if ok else "FAIL")
sys.exit(0 if ok else 1)
