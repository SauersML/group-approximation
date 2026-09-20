"""Numerical check of the pair-tent estimates.

Node: full-shift-full-group-has-no-infinite-relative-fh-subsets (Step 3 of its route).

The points are long random words standing in for aperiodic points. The pair orbit point
(sigma^a x, sigma^b x') is encoded as (a, b), which is faithful because x and x' are aperiodic.
For each witness y and each fixed element g, we compute psi_f(g) = ||g f - f||^2 exactly, where
f is the tent of radius R on the diagonal {(c, c)}.

Expected: psi_f(y) >= 1, and psi_f(g) <= (2R + 2K - 1) K^2 / R^2, which tends to 0.
"""
import random

N = 4000          # half-length of the simulated words
rng = random.Random(20260920)
Z = [rng.randint(0, 1) for _ in range(2 * N + 1)]   # z, indexed by n + N


def word(base, forced):
    w = list(base)
    for n, v in forced.items():
        w[n + N] = v
    return w


def cyl(pattern_lo, pattern):   # membership test for a cylinder {y_{lo+i} = pattern[i]}
    return lambda acc: all(acc(pattern_lo + i) == b for i, b in enumerate(pattern))


def swap(member):
    """k for s_E: +1 on E, -1 on sigma E, 0 elsewhere (requires E and sigma E disjoint)."""
    def k(acc):
        if member(acc):
            return 1
        if member(lambda n: acc(n - 1)):   # y in sigma E  iff  sigma^{-1} y in E
            return -1
        return 0
    return k


def acc_at(w, c):   # coordinates of sigma^c w
    return lambda n: w[n + c + N]


def psi_pair(k, x, xp, R):
    f = {(c, c): 1 - abs(c) / R for c in range(-R + 1, R)}
    gf = {}
    for (a, b), v in f.items():
        gf[(a + k(acc_at(x, a)), b + k(acc_at(xp, b)))] = v
    keys = set(f) | set(gf)
    return sum((gf.get(p, 0) - f.get(p, 0)) ** 2 for p in keys)


E = cyl(-1, [1, 0])
fixed = {
    "shift": (lambda acc: 1, 1),
    "s_E": (swap(E), 1),
    "g_3": (swap(cyl(-3, Z[N - 3:N + 4])), 1),
}


def report(name, ky, x, xp, R):
    print(f"{name}: R={R} psi(y)={psi_pair(ky, x, xp, R):.3f}", end="")
    for gname, (kg, K) in fixed.items():
        val = psi_pair(kg, x, xp, R)
        bound = (2 * R + 2 * K - 1) * K * K / R ** 2
        assert val <= bound + 1e-12, (gname, val, bound)
        print(f"  {gname}={val:.4f}(<= {bound:.4f})", end="")
    print()


for m in [8, 16, 32, 64, 128]:
    E_m = cyl(-m, Z[N - m:N + m + 1])
    x = word(Z, {})                        # x in E_m
    xp = word(Z, {m: 1 - Z[N + m]})        # flip the far site m
    ky = swap(E_m)
    assert ky(acc_at(x, 0)) != ky(acc_at(xp, 0))
    report(f"g_{m}", ky, x, xp, m // 2)

for i in [8, 16, 32, 64, 128]:
    R_i = cyl(-1, [1] + [0] * (i + 1) + [1])
    forced = {-1: 1, i + 1: 1}
    forced.update({n: 0 for n in range(0, i + 1)})
    x = word(Z, forced)
    xp = word(Z, {**forced, i + 1: 0})     # flip the site i+1
    ky = swap(R_i)
    assert ky(acc_at(x, 0)) != ky(acc_at(xp, 0))
    report(f"r_{i}", ky, x, xp, (i + 1) // 2)
