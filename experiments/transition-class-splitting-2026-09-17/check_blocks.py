"""Checks for block-permutation-transitions-force-divisible-classes.

1. Random relations R containing a k-block permutation E: every class size is divisible by k.
2. lambda o (K_k (x) S) o lambda' with S containing a permutation (S = transition digraph of an
   injective automaton sigma): every class size divisible by k.
3. Necessity of the permutation: S without a permutation can give class sizes prime to k.
4. Capacity lifts of a relation containing E: n monotone forces n constant on P_b u T_f(b).
"""
import math, random, sys
from search import classes

random.seed(7)


def block_perm(k, m):
    n = k * m
    lets = list(range(n))
    random.shuffle(lets); P = [lets[i * k:(i + 1) * k] for i in range(m)]
    random.shuffle(lets); T = [lets[i * k:(i + 1) * k] for i in range(m)]
    f = list(range(m)); random.shuffle(f)
    E = {v: set() for v in range(n)}
    for b in range(m):
        for p in P[b]:
            E[p] |= set(T[f[b]])
    return n, E, P, T, f


def check1(trials=3000):
    bad = 0
    for _ in range(trials):
        k = random.choice([2, 3, 5]); m = random.randint(1, 5)
        n, E, P, T, f = block_perm(k, m)
        extra = random.random() * 3.0 / n
        adj = {v: sorted(E[v] | {w for w in range(n) if random.random() < extra}) for v in range(n)}
        sizes, ok = classes(n, adj)
        if not ok or any(s % k for s in sizes):
            bad += 1
    return bad


def rand_S_with_perm(m, dens):
    p = list(range(m)); random.shuffle(p)
    return {b: sorted({p[b]} | {c for c in range(m) if random.random() < dens}) for b in range(m)}


def check2(trials=3000):
    bad = 0; seen = set()
    for _ in range(trials):
        k = random.choice([3, 5]); m = random.randint(1, 5)
        S = rand_S_with_perm(m, random.random() * 0.5)
        n = k * m
        lam = list(range(n)); random.shuffle(lam)
        lam2 = list(range(n)); random.shuffle(lam2)
        # letter (a, b) -> index a*m + b; R0 = K_k (x) S
        R0 = {a * m + b: [a2 * m + b2 for a2 in range(k) for b2 in S[b]] for a in range(k) for b in range(m)}
        inv2 = {lam2[i]: i for i in range(n)}
        # R(lambda o Phi o lambda2) = {(lambda2^-1 u, lambda v) : (u, v) in R0}
        adj = {inv2[u]: [lam[v] for v in R0[u]] for u in range(n)}
        sizes, ok = classes(n, adj)
        seen.add(tuple(sizes))
        if any(s % k for s in sizes):
            bad += 1
    return bad, len(seen)


def check3():
    # S on 2 vertices: 0 -> 1 only, 1 -> 0, 1 (no permutation: 0 has no preimage... check)
    # Use S = {0: [1], 1: [1]}: contains no permutation (0 is never a target).
    k, m = 3, 2
    S = {0: [1], 1: [1]}
    R0 = {a * m + b: [a2 * m + b2 for a2 in range(k) for b2 in S[b]] for a in range(k) for b in range(m)}
    sizes, ok = classes(k * m, R0)
    return sizes, ok


def check4(trials=2000):
    bad = 0
    for _ in range(trials):
        k = random.choice([2, 3]); m = random.randint(1, 4)
        n, E, P, T, f = block_perm(k, m)
        # random monotone n along E (not along extra edges): search small values
        vals = [random.randint(1, 3) for _ in range(n)]
        mono = all(vals[p] <= vals[t] for p in range(n) for t in E[p])
        if mono:
            for b in range(m):
                if len({vals[x] for x in P[b] + T[f[b]]}) != 1:
                    bad += 1
    return bad


if __name__ == "__main__":
    print("check1 bad:", check1())
    print("check2 bad, distinct size profiles:", check2())
    print("check3 sizes, all-on-cycle:", check3())
    print("check4 bad:", check4())
