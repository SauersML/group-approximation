"""Check the k-subset fixed-fraction sandwich used in
research/configuration-product-models-reduce-to-point-models-proof.md (Step 1):

    for g in Sym(m), b = moved fraction on points, phi = fixed fraction on k-subsets,
    m >= 8 k^2  ==>  1 - 2 k b <= phi <= 1 - b/2.

The number of g-invariant k-subsets is the x^k coefficient of prod_j (1+x^j)^{c_j},
c_j = number of j-cycles.  We test random permutations and adversarial cycle types
(many 2-cycles, one long cycle, many 3-cycles, few moved points).  Exact arithmetic.
"""
import random
from math import comb
from fractions import Fraction


def invariant_subsets(cycle_lengths, k):
    poly = [1] + [0] * k
    for L in cycle_lengths:
        if L > k:
            continue  # (1 + x^L) contributes only its constant term in degrees <= k
        new = poly[:]
        for d in range(k - L, -1, -1):
            new[d + L] += poly[d]
        poly = new
    return poly[k]


def cycles_of(perm):
    seen, out = set(), []
    for s in range(len(perm)):
        if s in seen:
            continue
        L, x = 0, s
        while x not in seen:
            seen.add(x)
            x = perm[x]
            L += 1
        out.append(L)
    return out


def check(cyc, m, k):
    assert sum(cyc) == m
    moved = sum(L for L in cyc if L > 1)
    b = Fraction(moved, m)
    phi = Fraction(invariant_subsets(cyc, k), comb(m, k))
    lo, hi = 1 - 2 * k * b, 1 - b / 2
    return lo <= phi <= hi, float(b), float(phi)


def main():
    rng = random.Random(20260917)
    bad = tests = 0
    for k in (1, 2, 3, 4):
        m0 = 8 * k * k
        for m in (m0, m0 + 7, 2 * m0, 300):
            families = []
            for moved in (0, 2, 3, m // 10, m // 3, m // 2, m):
                families.append([2] * (moved // 2) + [1] * (m - 2 * (moved // 2)))
                if moved >= 2:
                    families.append([moved] + [1] * (m - moved))
                    families.append([3] * (moved // 3) + [1] * (m - 3 * (moved // 3)))
            for _ in range(40):
                p = list(range(m))
                rng.shuffle(p)
                families.append(cycles_of(p))
                pts = rng.sample(range(m), rng.randint(0, m))
                q, sh = list(range(m)), pts[:]
                rng.shuffle(sh)
                for a, c in zip(pts, sh):
                    q[a] = c
                families.append(cycles_of(q))
            for cyc in families:
                ok, b, phi = check(cyc, m, k)
                tests += 1
                if not ok:
                    bad += 1
                    print("VIOLATION", k, m, sorted(cyc)[-5:], b, phi)
    print(f"tests={tests} violations={bad}")


if __name__ == "__main__":
    main()
