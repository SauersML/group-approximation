#!/usr/bin/env python3
"""Numerical check of the bounded-depth character asymptotic.

Claim (Lemma CA of research/bounded-depth-symmetric-models-are-sofic-approximations-proof.md):
for lambda = (m - j, mu), mu a partition of j, and every sigma in S_m,

    | chi^lambda(sigma) / dim lambda  -  (F(sigma)/m)^j |  <=  C_j / m,

with F(sigma) the number of fixed points and C_j independent of m.

We compute characters exactly by the Murnaghan--Nakayama rule (independent of
the Young's-rule proof) and report max over cycle types of m * |r - f^j|,
which must stay bounded as m grows.
"""
from functools import lru_cache
import random
import sys


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def to_beta(lam):
    """beta-set (first-column hook lengths) of a partition."""
    L = len(lam)
    return tuple(lam[i] + (L - 1 - i) for i in range(L))


@lru_cache(maxsize=None)
def mn(beta, rho):
    """Murnaghan--Nakayama on beta-sets: chi^lambda(rho), rho a tuple of cycle lengths."""
    if not rho:
        return 1
    k = rho[0]
    rest = rho[1:]
    s = set(beta)
    total = 0
    for b in beta:
        if b - k >= 0 and (b - k) not in s:
            # removing a border strip of length k; sign = (-1)^(number of beta between)
            between = sum(1 for c in beta if b - k < c < b)
            nb = tuple(sorted((s - {b}) | {b - k}, reverse=True))
            total += (-1) ** between * mn(nb, rest)
    return total


def hook_dim(lam):
    from math import factorial
    n = sum(lam)
    conj = [sum(1 for r in lam if r > c) for c in range(lam[0])] if lam else []
    prod = 1
    for i, r in enumerate(lam):
        for c in range(r):
            prod *= (r - c - 1) + (conj[c] - i - 1) + 1
    return factorial(n) // prod


def random_cycle_type(m, rng):
    # random permutation's cycle type, plus biased variants with many fixed points
    mode = rng.random()
    perm = list(range(m))
    rng.shuffle(perm)
    if mode < 0.5:
        # keep a random fraction of points fixed
        keep = rng.randint(0, m)
        fixed = set(rng.sample(range(m), keep))
        moved = [i for i in range(m) if i not in fixed]
        sh = moved[:]
        rng.shuffle(sh)
        perm = list(range(m))
        for a, b in zip(moved, sh):
            perm[a] = b
    seen = [False] * m
    cyc = []
    for i in range(m):
        if not seen[i]:
            l = 0
            j = i
            while not seen[j]:
                seen[j] = True
                j = perm[j]
                l += 1
            cyc.append(l)
    return tuple(sorted(cyc, reverse=True))


def main():
    rng = random.Random(20260918)
    D = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    ms = [int(x) for x in sys.argv[2:]] or [16, 24, 32, 48, 64]
    print("D =", D)
    for m in ms:
        worst = {}
        types = set(random_cycle_type(m, rng) for _ in range(300))
        types |= {tuple([1] * m), tuple([2] + [1] * (m - 2)), tuple([2] * (m // 2) + [1] * (m % 2)),
                  tuple([3] * (m // 3) + [1] * (m % 3)), (m,)}
        for j in range(1, D + 1):
            for mu in partitions(j):
                lam = (m - j,) + mu
                beta = to_beta(lam)
                d = hook_dim(lam)
                w = 0.0
                for rho in types:
                    F = rho.count(1)
                    r = mn(beta, rho) / d
                    w = max(w, m * abs(r - (F / m) ** j))
                worst[(j, mu)] = w
        print(f"m={m:3d} ", "  ".join(f"{mu}:{v:6.2f}" for (j, mu), v in sorted(worst.items())))
        mn.cache_clear()


if __name__ == "__main__":
    main()
