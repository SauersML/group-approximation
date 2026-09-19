"""Check the two-sided k-subset displacement lemma of
research/subset-models-are-point-models-at-every-size-proof.md (Lemma D):

    for g in Sym(m) moving M points, b = M/m, 1 <= k <= m-1, k' = min(k, m-k),
    mu_k(g) = fraction of k-subsets moved by g satisfies

        min(1, k' b) / 6  <=  mu_k(g)  <=  min(1, k' b).

No hypothesis relating k and m.  The number of g-invariant k-subsets is the x^k
coefficient of prod over cycles (1 + x^len).  Exact rational arithmetic.

Part A: every cycle type (partition) of m for m <= MMAX, every k.
Part B: adversarial and random cycle types for m up to 600, all k, with emphasis on the
        range sqrt(m/8) < k = o(m) left open by Theorem CP (many 2-cycles).
Part C: the ratio transfer (CP') on random block data: for random trivial-top wreath
        data, h_conf/d_conf <= 7 max(1, h_pt/d_pt).

Prints the worst observed value of mu_k / min(1, k' b) and any violation.
"""
import random
from math import comb, isqrt
from fractions import Fraction

MMAX = 26


def invariant_subsets(cycle_lengths, k):
    poly = [1] + [0] * k
    for L in cycle_lengths:
        if L > k:
            continue
        new = poly[:]
        for d in range(k - L, -1, -1):
            new[d + L] += poly[d]
        poly = new
    return poly[k]


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield []
        return
    for p in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - p, p):
            yield [p] + rest


def mu(cyc, k):
    m = sum(cyc)
    return 1 - Fraction(invariant_subsets(cyc, k), comb(m, k))


def scale(cyc, k):
    m = sum(cyc)
    M = sum(L for L in cyc if L > 1)
    kp = min(k, m - k)
    return min(Fraction(1), Fraction(kp * M, m))


def check_one(cyc, k, stats):
    s = scale(cyc, k)
    u = mu(cyc, k)
    stats["tests"] += 1
    if s == 0:
        if u != 0:
            stats["bad"] += 1
        return
    if not (s / 6 <= u <= s):
        stats["bad"] += 1
        print("VIOLATION", sorted(cyc, reverse=True)[:12], "m", sum(cyc), "k", k, float(u), float(s))
    r = u / s
    if r < stats["worst"]:
        stats["worst"] = r
        stats["worst_at"] = (sum(cyc), k, sorted(cyc, reverse=True)[:8])


def part_a(stats):
    for m in range(2, MMAX + 1):
        for cyc in partitions(m):
            for k in range(1, m):
                check_one(cyc, k, stats)


def part_b(stats, rng):
    for m in (50, 97, 128, 200, 333, 600):
        fams = []
        for c in (1, 2, 3, m // 20, m // 8, m // 4, m // 2):
            if 2 * c <= m:
                fams.append([2] * c + [1] * (m - 2 * c))
        for c in (1, 2, m // 30, m // 9, m // 3):
            if c >= 1 and 3 * c <= m:
                fams.append([3] * c + [1] * (m - 3 * c))
        fams.append([m])
        fams.append([m - 1, 1])
        fams.append([m // 2, m - m // 2])
        for _ in range(12):
            left, cyc = m, []
            while left > 0:
                L = rng.choice([1, 1, 1, 2, 2, 3, 4, 7, rng.randint(1, left)])
                L = min(L, left)
                cyc.append(L)
                left -= L
            fams.append(cyc)
        ks = sorted(set([1, 2, 3, isqrt(m // 8), isqrt(m // 8) + 1, isqrt(m), 2 * isqrt(m),
                         m // 10, m // 4, m // 3, m // 2, m - 1, m - isqrt(m)]))
        ks = [k for k in ks if 1 <= k <= m - 1]
        for cyc in fams:
            for k in ks:
                check_one(cyc, k, stats)


def part_c(stats, rng):
    """Ratio transfer on random trivial-top data: each word is an l-tuple of cycle types."""
    worst = Fraction(0)
    for _ in range(400):
        m = rng.randint(4, 40)
        k = rng.randint(1, m - 1)
        l = rng.randint(1, 6)

        def rand_block(p):
            cyc, left = [], m
            while left > 0:
                L = 1 if rng.random() > p else rng.randint(2, max(2, min(left, 5)))
                L = min(L, left)
                cyc.append(L)
                left -= L
            return cyc

        head = [rand_block(rng.random()) for _ in range(l)]
        rels = [[rand_block(rng.random() * 0.3) for _ in range(l)] for _ in range(3)]

        def conf(word):
            fix = Fraction(1)
            for cyc in word:
                fix *= 1 - mu(cyc, k)
            return 1 - fix

        def pt(word):
            return Fraction(sum(sum(L for L in cyc if L > 1) for cyc in word), m * l)

        hc, hp = conf(head), pt(head)
        dc = max(conf(r) for r in rels)
        dp = max(pt(r) for r in rels)
        if dp == 0 or dc == 0:
            continue
        lhs = hc / dc
        rhs = 7 * max(Fraction(1), hp / dp)
        stats["ctests"] += 1
        if lhs > rhs:
            stats["cbad"] += 1
            print("RATIO VIOLATION", m, k, l, float(lhs), float(rhs))
        worst = max(worst, lhs / rhs)
    stats["cworst"] = worst


def main():
    rng = random.Random(20260918)
    stats = {"tests": 0, "bad": 0, "worst": Fraction(10**9), "worst_at": None, "ctests": 0, "cbad": 0}
    part_a(stats)
    na = stats["tests"]
    part_b(stats, rng)
    part_c(stats, rng)
    print(f"lemma tests={stats['tests']} (exhaustive m<={MMAX}: {na}) violations={stats['bad']}")
    print(f"worst mu/min(1,k'b) = {float(stats['worst']):.4f} at (m,k,cycles)={stats['worst_at']}")
    print(f"ratio-transfer tests={stats['ctests']} violations={stats['cbad']} "
          f"worst (h_c/d_c)/(7 max(1,h_p/d_p)) = {float(stats['cworst']):.4f}")


if __name__ == "__main__":
    main()
