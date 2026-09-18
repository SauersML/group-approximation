#!/usr/bin/env python3
"""Numerical sanity checks for the sqrt-scale unique games equivalence.

Checks
  1. 2 sqrt(1-g)/(2-g) <= exp(-g^2/8) on a fine grid of g in (0,1].
  2. Parameter arithmetic of the amplification direction: with
     C^2 = 32 ln(1/delta)/eps, eta <= 1/C^2, t = floor(eps/eta):
     t >= 1, 1 - t*eta >= 1 - eps, exp(-C^2 eta t/16) <= delta.
  3. Squaring-law arithmetic: R >= 6, eta0 <= 1/R^2,
     t = ceil(16/(R^2 eta0)) gives t*eta0 <= 17/R^2 and
     exp(-R^2 eta0 t/16) <= 1/e.
  4. Exact values of random small bipartite unique games and of their
     2-fold tensor: val2 >= val^2 and val2^2 <= (2 sqrt(d)/(1+d))^2
     (Dinur--Steurer, two copies, d = val).
  5. Odd cycle game C_m (m = 3, 5): value 1 - 1/(2m), and the 2-fold
     repeated value for m = 3.
Exits nonzero on any violation.
"""
import itertools
import math
import random
import sys

FAIL = []


def check_constants():
    worst = -1.0
    n = 200000
    for i in range(1, n + 1):
        g = i / n
        lhs = 2 * math.sqrt(1 - g) / (2 - g)
        rhs = math.exp(-g * g / 8)
        worst = max(worst, lhs - rhs)
    print(f"[1] max over grid of 2sqrt(1-g)/(2-g) - exp(-g^2/8) = {worst:.3e}")
    if worst > 1e-12:
        FAIL.append("constants")


def check_parameters():
    bad = 0
    count = 0
    for eps in [0.4, 0.2, 0.1, 0.05, 0.01, 0.003]:
        for delta in [0.5, 0.2, 0.1, 0.01, 1e-4]:
            if delta > math.exp(-1 / 32):
                continue
            C2 = 32 * math.log(1 / delta) / eps
            for frac in [1.0, 0.9, 0.51, 0.37, 0.1, 0.013]:
                eta = frac / C2
                t = math.floor(eps / eta)
                comp = 1 - t * eta
                sound = math.exp(-C2 * eta * t / 16)
                count += 1
                if not (t >= 1 and comp >= 1 - eps - 1e-15
                        and sound <= delta * (1 + 1e-12)
                        and C2 * eta <= 1 + 1e-12):
                    bad += 1
    print(f"[2] amplification parameter cases: {count}, violations: {bad}")
    if bad:
        FAIL.append("parameters")
    bad = 0
    count = 0
    for R in [6, 7, 10, 30, 100]:
        for frac in [1.0, 0.5, 0.1, 0.01, 0.0013]:
            eta0 = frac / R ** 2
            t = math.ceil(16 / (R * R * eta0))
            count += 1
            if not (t * eta0 <= 17 / R ** 2 + 1e-15
                    and math.exp(-R * R * eta0 * t / 16) <= math.exp(-1) + 1e-15
                    and 17 / R ** 2 < 1 - math.exp(-1)):
                bad += 1
    print(f"[3] squaring-law parameter cases: {count}, violations: {bad}")
    if bad:
        FAIL.append("squaring")


def value(edges, nU, nV, k):
    """Exact value of a bipartite unique game.

    edges: list of (u, v, perm) with perm a tuple, constraint perm[a] == b.
    Brute force over Alice labellings, Bob best-responds.
    """
    best = 0
    by_v = [[] for _ in range(nV)]
    for (u, v, p) in edges:
        by_v[v].append((u, p))
    for f in itertools.product(range(k), repeat=nU):
        tot = 0
        for v in range(nV):
            cnt = [0] * k
            for (u, p) in by_v[v]:
                cnt[p[f[u]]] += 1
            tot += max(cnt) if by_v[v] else 0
        best = max(best, tot)
    return best / len(edges)


def tensor(edges, nU, nV, k):
    out = []
    for (u1, v1, p1), (u2, v2, p2) in itertools.product(edges, repeat=2):
        perm = tuple(p1[a // k] * k + p2[a % k] for a in range(k * k))
        out.append((u1 * nU + u2, v1 * nV + v2, perm))
    return out, nU * nU, nV * nV, k * k


def check_small_games(trials=40, seed=17):
    rng = random.Random(seed)
    k, nU, nV, m = 2, 2, 3, 5
    perms = list(itertools.permutations(range(k)))
    bad = 0
    tight = 0
    for _ in range(trials):
        edges = [(rng.randrange(nU), rng.randrange(nV), rng.choice(perms))
                 for _ in range(m)]
        d = value(edges, nU, nV, k)
        G2 = tensor(edges, nU, nV, k)
        d2 = value(*G2)
        ds = 2 * math.sqrt(d) / (1 + d)
        if d2 < d * d - 1e-12 or d2 * d2 > ds * ds + 1e-12:
            bad += 1
        if d < 1 and d2 > d * d + 1e-12:
            tight += 1
    print(f"[4] random UG (k=2,|U|=2,|V|=3,5 edges): {trials} trials, "
          f"violations: {bad}, cases with val2 > val^2: {tight}")
    if bad:
        FAIL.append("small-games")


def odd_cycle(m):
    # Raz's odd cycle game: Alice gets x uniform, Bob gets x w.p. 1/2 and
    # x+1, x-1 w.p. 1/4 each (encoded by edge multiplicities 2,1,1);
    # answers in {0,1}; equal question: equal answers; adjacent: different.
    edges = []
    for x in range(m):
        edges.append((x, x, (0, 1)))
        edges.append((x, x, (0, 1)))
        edges.append((x, (x + 1) % m, (1, 0)))
        edges.append((x, (x - 1) % m, (1, 0)))
    return edges, m, m, 2


def check_odd_cycle():
    for m in [3, 5]:
        v = value(*odd_cycle(m))
        ok = abs(v - (1 - 1 / (2 * m))) < 1e-12
        print(f"[5] odd cycle C_{m}: value {v:.6f}, expected {1 - 1/(2*m):.6f}, ok={ok}")
        if not ok:
            FAIL.append(f"odd-cycle-{m}")
    G = odd_cycle(3)
    v2 = value(*tensor(*G))
    v1 = 1 - 1 / 6
    print(f"[5] odd cycle C_3 2-fold: value {v2:.6f}; val^2 = {v1*v1:.6f}; "
          f"DS bound sqrt(prod) = {2*math.sqrt(v1)/(1+v1):.6f}")
    if v2 < v1 * v1 - 1e-12 or v2 > 2 * math.sqrt(v1) / (1 + v1) + 1e-12:
        FAIL.append("odd-cycle-2fold")


if __name__ == "__main__":
    check_constants()
    check_parameters()
    check_small_games()
    check_odd_cycle()
    print("RESULT:", "FAIL " + ",".join(FAIL) if FAIL else "all checks passed")
    sys.exit(1 if FAIL else 0)
