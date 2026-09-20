#!/usr/bin/env python3
"""Checks for planted-regular-3lin-inputs-are-robustly-unique.

Part A  exact-rational check of the constant chain of the route (Steps 4-6)
        at the worst admissible parameters, for k = 3..200.
Part B  q(p) = 3p - 6p^2 + 4p^3: derivative identity and monotonicity on a grid.
Part C  |q_n(w) - q(w/n)| <= 3/n for the exact hypergeometric q_n, n <= 240.
Part D  the slot-measure bounds of Step 1 by exact enumeration of all
        legitimate ordered k-tuples on small D-regular instances.
Part E  brute force over all 2^n assignments on small planted instances:
        expansion profile and the robust-uniqueness radius (illustration only;
        the proof is asymptotic).
Deterministic: fixed seeds. Runtime about a minute.
"""
from fractions import Fraction as F
from itertools import permutations
import math
import random
import numpy as np

ok_all = True


def check(cond, msg):
    global ok_all
    if not cond:
        ok_all = False
        print("FAIL:", msg)
    return cond


# ---------------------------------------------------------------- Part A
def q(p):
    return 3 * p - 6 * p * p + 4 * p ** 3


def part_a():
    gamma = F(105, 1000)            # gamma <= 0.105, worst case
    beta0 = F(11, 100)              # beta0 < 0.11, worst case
    n_ok = 0
    for k in range(3, 201):
        keps = gamma / 4            # worst case k*eps = gamma/4
        eps = keps / k
        kappa = eps + gamma / (4 * k)   # gamma' < gamma
        p0 = F(6, 100) / k
        theta = F(9, 100) / k
        rho = F(61, 1000) / k
        # n0 = max(300k, 900k^2, 36k^2/eps); delta = 9k^2/n <= 1/100 and <= eps/4
        n0 = max(300 * k, 900 * k * k, math.ceil(36 * k * k / eps))
        delta = F(9 * k * k, n0)
        check(delta <= F(1, 100) and delta <= eps / 4, f"delta k={k}")
        # Step 6: viol^hom_unif(z) <= (kappa + (3/4)eps/(1-delta))/(1-delta) < theta
        vz = (kappa + F(3, 4) * eps / (1 - delta)) / (1 - delta)
        check(vz < theta, f"viol chain k={k}: {float(vz*k)} vs 0.09")
        # Step 3: q(p0) - 3/n >= theta + (0.0728)/k  (the Azuma gap)
        gap = q(p0) - F(3, n0) - theta
        check(gap >= F(728, 10000) / k, f"gap k={k}: {float(gap*k)}")
        # Step 3 exponent: t = gap * Dn/3, t^2/(8 n D) = gap^2 D n / 72;
        # with D >= 2*10^4 k^2 this is >= 1.47 n > (ln 2) n
        expo_per_n = gap * gap * 20000 * k * k / 72
        check(expo_per_n >= F(147, 100), f"azuma exponent k={k}: {float(expo_per_n)}")
        # Step 6: nu(supp z) < p0/(1-delta) <= rho < (1-beta0)/(12k)
        check(p0 / (1 - delta) <= rho, f"rho k={k}")
        check(rho < (1 - beta0) / (12 * k), f"rho vs Corollary M k={k}")
        # Step 5 (NO): (1/2+eps/2)/(1-delta) <= 1/2 + eps
        check((F(1, 2) + eps / 2) / (1 - delta) <= F(1, 2) + eps, f"NO k={k}")
        # Step 4 (YES): (3/4)eps/(1-delta) <= eps
        check(F(3, 4) * eps / (1 - delta) <= eps, f"YES k={k}")
        n_ok += 1
    # Step 5 exponent (Azuma binomial tail, s = eps/2) with D >= 20/eps^2:
    # D n eps^2/24 - n ln 2 >= (5/6 - ln 2) n >= 0.14 n
    check(F(5, 6) - F(6931472, 10 ** 7) >= F(14, 100), "Hoeffding margin")
    print(f"Part A: constant chain verified for k = 3..200 ({n_ok} values)")


# ---------------------------------------------------------------- Part B
def part_b():
    worst = 0.0
    prev = -1.0
    for i in range(0, 100001):
        p = i / 100000
        d_num = (q(p + 1e-7) - q(p - 1e-7)) / 2e-7
        worst = max(worst, abs(d_num - 3 * (1 - 2 * p) ** 2))
        check(q(p) >= prev - 1e-15, f"monotone at {p}")
        prev = q(p)
    # exact identity 3p-6p^2+4p^3 = (1 - (1-2p)^3)/2 at rationals
    for i in range(0, 101):
        p = F(i, 100)
        check(q(p) == (1 - (1 - 2 * p) ** 3) / 2, "closed form")
    print(f"Part B: q' = 3(1-2p)^2 (max numeric deviation {worst:.2e}); "
          f"q increasing on [0,1]; q = (1-(1-2p)^3)/2 exactly")


# ---------------------------------------------------------------- Part C
def part_c():
    worst = F(0)
    for n in range(3, 241):
        tot = math.comb(n, 3)
        for w in range(0, n + 1):
            odd = w * math.comb(n - w, 2) + math.comb(w, 3)
            qn = F(odd, tot)
            dev = abs(qn - q(F(w, n))) * n
            worst = max(worst, dev)
            check(dev <= 3, f"TV bound n={n} w={w}")
    print(f"Part C: max n*|q_n(w)-q(w/n)| over n<=240 is {float(worst):.4f} <= 3")


# ---------------------------------------------------------------- Part D
def triangle_factors(n, D, rng):
    eqs = []
    for _ in range(D):
        perm = list(range(n))
        rng.shuffle(perm)
        eqs += [tuple(perm[3 * j:3 * j + 3]) for j in range(n // 3)]
    return eqs


def part_d():
    rng = random.Random(20260920)
    cases = [(12, 2, 2), (15, 2, 2), (18, 2, 3), (21, 2, 3), (15, 3, 2)]
    for (n, D, k) in cases:
        eqs = triangle_factors(n, D, rng)
        m = len(eqs)
        assert m == D * n // 3
        sets = [set(e) for e in eqs]
        cnt = [0] * m
        total = 0
        for tup in permutations(range(m), k):
            good = True
            for i in range(k):
                for j in range(i + 1, k):
                    if sets[tup[i]] & sets[tup[j]]:
                        good = False
                        break
                if not good:
                    break
            if good:
                total += 1
                for s in tup:
                    cnt[s] += 1
        omega = [F(c, k * total) for c in cnt]
        check(sum(omega) == 1, "omega sums to 1")
        lo = F(1, m) * F(math.prod(m - 3 * D * j for j in range(1, k)), m ** (k - 1))
        hi = F(1, m) * F(m ** (k - 1), max(1, math.prod(m - 3 * D * j for j in range(1, k))))
        check(all(lo <= w <= hi for w in omega), f"omega bounds n={n}")
        # nu(v) = (1/(3k)) E[# variable slots equal v] = (1/3) sum_{e ni v} omega(e)
        nu = [sum(omega[i] for i in range(m) if v in sets[i]) / 3 for v in range(n)]
        check(sum(nu) == 1, "nu sums to 1")
        check(all(D * lo / 3 <= x <= D * hi / 3 for x in nu), f"nu bounds n={n}")
        print(f"Part D: n={n} D={D} k={k} m={m}: {total} legitimate tuples; "
              f"m*omega in [{float(min(omega))*m:.3f},{float(max(omega))*m:.3f}] "
              f"within [{float(lo*m):.3f},{float(hi*m):.3f}]")


# ---------------------------------------------------------------- Part E
def part_e():
    rng = random.Random(7)
    nprng = np.random.default_rng(7)
    for (n, D, noise) in [(18, 12, 0.02), (18, 24, 0.02), (21, 16, 0.03)]:
        eqs = triangle_factors(n, D, rng)
        m = len(eqs)
        xs = nprng.integers(0, 2, n)
        b = np.array([(xs[a] + xs[bb] + xs[c]) % 2 for (a, bb, c) in eqs])
        b ^= (nprng.random(m) < noise).astype(b.dtype)
        zs = np.arange(2 ** n, dtype=np.uint32)
        odd = np.zeros(2 ** n, dtype=np.int32)
        for (a, bb, c) in eqs:
            odd += ((zs >> a) ^ (zs >> bb) ^ (zs >> c)) & 1
        wt = np.zeros(2 ** n, dtype=np.int32)
        for v in range(n):
            wt += (zs >> v) & 1
        # expansion profile: min fraction of odd equations at each weight
        prof = [int(odd[wt == w].min()) / m for w in range(1, n // 2 + 1)]
        # values of all assignments a = x* + z: violated iff (z odd) xor (noise)
        xint = int(sum(int(xs[v]) << v for v in range(n)))
        viol = np.zeros(2 ** n, dtype=np.int32)
        aa = zs ^ np.uint32(xint)
        for i, (a, bb, c) in enumerate(eqs):
            viol += (((aa >> a) ^ (aa >> bb) ^ (aa >> c)) & 1) ^ int(b[i])
        # viol is indexed by z; z = 0 is x*
        v_star = int(viol[0])
        best = int(viol.min())
        rad = {}
        for thr in (0.05, 0.10, 0.15):
            sel = viol <= v_star + thr * m
            rad[thr] = int(wt[sel].max())
        check(np.all(odd <= viol + v_star), "odd <= viol(a) + viol(x*)")
        print(f"Part E: n={n} D={D} m={m} viol(x*)={v_star} min viol={best}; "
              f"min odd fraction at weight 1..{n//2}: "
              + " ".join(f"{p:.2f}" for p in prof)
              + "; max weight of a+x* among a with viol <= viol(x*)+t*m: "
              + ", ".join(f"t={t}: {r}" for t, r in rad.items()))


if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
    part_e()
    print("ALL CHECKS PASSED" if ok_all else "SOME CHECK FAILED")
