#!/usr/bin/env python3
"""Calibration checks for cluster-entropy-lower-bounds-need-nonpositive-total-weight.

Checks:
  1. Co-information of coordinate partitions of an i.i.d. uniform field equals
     |intersection| * log q (exact enumeration on small index sets).
  2. Joining an independent uniform m-point partition R shifts every H(P^V) by
     log m and every co-information I_U by log m, so a cluster functional
     shifts by kappa * log m (exact enumeration).
  3. H(R_E) = h(eps) + eps log m for the marker partition of the generator Q.
  4. Product-of-trees square complex for F_2 x F_2: kappa = chi(quotient) = 1,
     and the full subcomplex on B_n x B_n has chi = 1 (Bernoulli normalization
     F(P_K) = log q), while Bowen's functional on F_r has kappa = 1 - r.
  5. The resulting numbers on Bernoulli x (m points): cluster value
     log q + kappa log m against the generator bound log q + h(eps) + eps log m.
"""
import itertools
import math
import random
from collections import Counter
from fractions import Fraction


def entropy_of_labels(labels, weights):
    tot = Counter()
    for lab, w in zip(labels, weights):
        tot[lab] += w
    return -sum(float(p) * math.log(float(p)) for p in tot.values() if p > 0)


def check_coinformation(q=2, n_coords=6, trials=40, seed=1):
    rng = random.Random(seed)
    pts = list(itertools.product(range(q), repeat=n_coords))
    w = [Fraction(1, q ** n_coords)] * len(pts)
    for _ in range(trials):
        k = rng.randint(1, 4)
        sets = [frozenset(rng.sample(range(n_coords), rng.randint(1, n_coords))) for _ in range(k)]
        # co-information by inclusion-exclusion over nonempty subfamilies
        coinf = 0.0
        for r in range(1, k + 1):
            for sub in itertools.combinations(range(k), r):
                union = sorted(set().union(*[sets[i] for i in sub]))
                labels = [tuple(p[j] for j in union) for p in pts]
                coinf += (-1) ** (r + 1) * entropy_of_labels(labels, w)
        inter = frozenset.intersection(*sets)
        assert abs(coinf - len(inter) * math.log(q)) < 1e-9, (sets, coinf)
    print(f"[1] co-information of coordinate partitions = |intersection| log q  ({trials} random families) OK")


def check_invariant_join_shift(q=2, n_coords=5, m=3, trials=30, seed=2):
    rng = random.Random(seed)
    pts = list(itertools.product(range(q), repeat=n_coords))
    space = [(p, c) for p in pts for c in range(m)]
    w = [Fraction(1, q ** n_coords * m)] * len(space)
    for _ in range(trials):
        k = rng.randint(1, 4)
        sets = [sorted(rng.sample(range(n_coords), rng.randint(1, n_coords))) for _ in range(k)]
        coeffs = [rng.randint(-3, 3) for _ in range(k)]
        kappa = sum(coeffs)
        F_plain = 0.0
        F_join = 0.0
        for S, cW in zip(sets, coeffs):
            F_plain += cW * entropy_of_labels([tuple(p[j] for j in S) for p, c in space], w)
            # R is invariant as a partition, so (P v R)^W = P^W v R
            F_join += cW * entropy_of_labels([(tuple(p[j] for j in S), c) for p, c in space], w)
        assert abs(F_join - F_plain - kappa * math.log(m)) < 1e-9
    print(f"[2] F((P v R)^W-family) = F(P^W-family) + kappa log m  ({trials} random functionals, m={m}) OK")


def check_marker_entropy():
    for m in (2, 5, 50, 10 ** 6):
        for eps in (0.5, 0.1, 1e-3):
            atoms = [1 - eps] + [eps / m] * min(m, 10 ** 4)
            if m > 10 ** 4:
                H = -(1 - eps) * math.log(1 - eps) - eps * math.log(eps / m)
            else:
                H = -sum(a * math.log(a) for a in atoms)
            h = -eps * math.log(eps) - (1 - eps) * math.log(1 - eps)
            assert abs(H - (h + eps * math.log(m))) < 1e-9
    print("[3] H(R_E) = h(eps) + eps log m OK")


# ---- F_2 x F_2 product of trees -------------------------------------------
GENS = "aAbB"
INV = {"a": "A", "A": "a", "b": "B", "B": "b"}


def ball(n):
    words = [""]
    frontier = [""]
    for _ in range(n):
        new = []
        for w in frontier:
            for s in GENS:
                if w and INV[s] == w[-1]:
                    continue
                new.append(w + s)
        words += new
        frontier = new
    return words


def mul(w, s):
    if w and INV[s] == w[-1]:
        return w[:-1]
    return w + s


def chi_full_subcomplex(K1, K2):
    """Full subcomplex of the product-of-trees square complex on K1 x K2.
    Cells: vertices (x,y); edges {(x,y),(xs,y)} and {(x,y),(x,yt)} for positive
    generators s,t in {a,b}; squares {(x,y),(xs,y),(x,yt),(xs,yt)}."""
    S1, S2 = set(K1), set(K2)
    V = len(S1) * len(S2)
    E1 = sum(1 for x in S1 for s in "ab" if mul(x, s) in S1)
    E2 = sum(1 for y in S2 for t in "ab" if mul(y, t) in S2)
    E = E1 * len(S2) + E2 * len(S1)
    Q = E1 * E2
    return V - E + Q


def check_square_complex():
    # quotient complex: 1 vertex, 4 edge orbits, 4 square orbits
    kappa = 1 - 4 + 4
    assert kappa == 1
    for n in range(0, 5):
        K = ball(n)
        assert chi_full_subcomplex(K, K) == 1, n
    # a non-convex exhaustion changes the normalization, recorded for contrast
    K = [w for w in ball(3) if len(w) != 2]
    print(f"    (non-convex set: chi = {chi_full_subcomplex(K, K)}; the theorem does not use convexity)")
    print("[4] F_2 x F_2 square complex: kappa = chi(quotient) = 1, chi(X[B_n x B_n]) = 1 for n<=4 OK")
    for r in range(1, 6):
        assert (1 - 2 * r) + r == 1 - r
    print("    Bowen functional (1-2r)H(Q) + sum_i H(Q v s_i Q): kappa = 1 - r <= 0 for r >= 1 OK")


def check_numbers():
    q = 2
    eps = 1e-3
    for m in (2, 16, 10 ** 3, 10 ** 9):
        h = -eps * math.log(eps) - (1 - eps) * math.log(1 - eps)
        upper = math.log(q) + h + eps * math.log(m)
        square = math.log(q) + 1 * math.log(m)
        bowen2 = math.log(q) + (1 - 2) * math.log(m)
        print(f"    m={m:>10}: square-complex F = {square:8.3f}   generator bound H(Q) = {upper:8.3f}   Bowen r=2 F = {bowen2:8.3f}")
    m = 10 ** 9
    h = -eps * math.log(eps) - (1 - eps) * math.log(1 - eps)
    assert math.log(q) + math.log(m) > math.log(q) + h + eps * math.log(m)
    print("[5] square-complex functional exceeds H(Q) on Bernoulli x (m points): not a lower bound OK")


if __name__ == "__main__":
    check_coinformation()
    check_invariant_join_shift()
    check_marker_entropy()
    check_square_complex()
    check_numbers()
    print("ALL CHECKS PASSED")
