"""Independent re-derivation of the l^infinity non-cnd certificate used by
`brin-thompson-nv-max-type-size-functions-are-not-cnd`.

Nothing here imports the original lane's code.  Three checks:

A. Zero-sum spectrum.  For the kernel K_beta(x,y) = ||x-y||_inf^beta on the grid
   S_k = {-k..k}^3, compute the largest eigenvalue of P K_beta P with
   P = I - J/|S|, the orthogonal projection onto the zero-sum subspace.  A cnd
   kernel has that quantity <= 0.  Reported for beta in {1, 1/2, 1/4, 1/8, 1/10}.

B. Exact certificate.  From the top zero-sum eigenvector build an *integer*
   zero-sum vector c, collect the distance-class sums
       N_d = sum_{||x-y||_inf = d} c_x c_y   (exact integers),
   and bound Q_beta = sum_d N_d d^beta from below by *rational interval*
   arithmetic: for each d we produce rationals a_d <= d^beta <= b_d certified by
   integer comparisons of the form a^q <= d^p (beta = p/q), and take
       Qlow = sum_{N_d > 0} N_d a_d + sum_{N_d < 0} N_d b_d.
   Qlow > 0 proves, with no floating point anywhere, that K_beta is not cnd on S_k.

C. Re-verification of the certificate stored by the audited lane
   (experiments/brin-thompson-cnd-2026-09-17/zcube_linf_certificates.json) with
   the same exact interval arithmetic, independently of that lane's Decimal code.

Usage:  python3 audit_linf_certificate.py
"""
import itertools
import json
import os
from fractions import Fraction

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LANE = os.path.join(os.path.dirname(HERE), "brin-thompson-cnd-2026-09-17")


# ---------------------------------------------------------------- exact roots
def root_bounds(d, p, q, digits=40):
    """Rationals a <= d^(p/q) <= b with b - a <= 10^-digits, certified by integers.

    Bisection on r = a/10^digits with the exact test (r)^q <= d^p.
    """
    target = d ** p                      # integer
    scale = 10 ** digits
    lo, hi = 0, (d + 2) * scale          # (d+2)^(p/q) > d^(p/q) for d>=1, p<=q
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** q <= target * scale ** q:
            lo = mid
        else:
            hi = mid - 1
    a = Fraction(lo, scale)
    b = Fraction(lo + 1, scale)
    assert a ** q <= Fraction(target) <= b ** q, (d, p, q)
    return a, b


# ------------------------------------------------------------------ the grids
def grid(k):
    return [np.array(x) for x in itertools.product(range(-k, k + 1), repeat=3)]


def dist_matrix(k):
    P = np.array(list(itertools.product(range(-k, k + 1), repeat=3)))
    return np.abs(P[:, None, :] - P[None, :, :]).max(-1)


def top_zero_sum(K):
    n = K.shape[0]
    P = np.eye(n) - np.ones((n, n)) / n
    M = P @ K @ P
    M = (M + M.T) / 2
    w, V = np.linalg.eigh(M)
    return w[-1], V[:, -1]


def integer_certificate(D, beta_pq, scale=10 ** 6):
    """Integer zero-sum c from the top zero-sum eigenvector, plus exact N_d and Qlow."""
    p, q = beta_pq
    beta = p / q
    lam, vec = top_zero_sum(D.astype(float) ** beta)
    c = [int(round(scale * float(x))) for x in vec]
    i0 = max(range(len(c)), key=lambda i: abs(c[i]))
    c[i0] -= sum(c)
    assert sum(c) == 0
    return lam, c, exact_Q(D, c, beta_pq)


def exact_Q(D, c, beta_pq):
    """N_d (exact ints) and a rational lower bound for Q = sum_d N_d d^beta."""
    p, q = beta_pq
    n = len(c)
    assert D.shape == (n, n)
    N = {}
    for i in range(n):
        ci = c[i]
        if ci == 0:
            continue
        row = D[i]
        for j in range(n):
            d = int(row[j])
            if d:
                N[d] = N.get(d, 0) + ci * c[j]
    Qlow = Fraction(0)
    Qhigh = Fraction(0)
    for d, Nd in sorted(N.items()):
        a, b = root_bounds(d, p, q)
        Qlow += Nd * (a if Nd > 0 else b)
        Qhigh += Nd * (b if Nd > 0 else a)
    return N, Qlow, Qhigh


def main():
    print("=" * 78)
    print("A. largest eigenvalue of the l^inf^beta kernel on the zero-sum subspace")
    print("   (cnd  <=>  this is <= 0)")
    print("=" * 78)
    for k in (1, 2, 3, 5):
        D = dist_matrix(k)
        Df = D.astype(float)
        row = []
        for name, beta in (("1", 1.0), ("1/2", 0.5), ("1/4", 0.25), ("1/8", 0.125), ("1/10", 0.1)):
            lam, _ = top_zero_sum(Df ** beta)
            row.append(f"beta={name}: {lam:+.6f}")
        print(f"  grid k={k} ({D.shape[0]:5d} pts)  " + "   ".join(row))

    print()
    print("=" * 78)
    print("B. independently derived exact integer certificates (no floating point"
          " in the final inequality)")
    print("=" * 78)
    for k, (p, q) in ((1, (1, 1)), (2, (1, 2)), (5, (1, 4))):
        D = dist_matrix(k)
        lam, c, (N, Qlow, Qhigh) = integer_certificate(D, (p, q))
        ok = Qlow > 0
        print(f"  grid k={k}, beta={p}/{q}: float top zero-sum eigenvalue {lam:+.6f}")
        print(f"    N_d = {dict(sorted(N.items()))}")
        print(f"    Q in [{float(Qlow):+.6e}, {float(Qhigh):+.6e}]  ->  "
              f"{'NOT CND (certified, exact)' if ok else 'no certificate'}")

    print()
    print("=" * 78)
    print("C. exact re-verification of the audited lane's stored certificates")
    print("=" * 78)
    path = os.path.join(LANE, "zcube_linf_certificates.json")
    certs = json.load(open(path))
    for cert in certs:
        k = cert["k"]
        beta = Fraction(cert["beta"])
        p, q = beta.numerator, beta.denominator
        c = cert["c"]
        D = dist_matrix(k)
        assert len(c) == D.shape[0], (len(c), D.shape)
        assert sum(c) == 0, "stored c is not zero-sum"
        N, Qlow, Qhigh = exact_Q(D, c, (p, q))
        stored = {int(d): v for d, v in cert["N_d"].items()}
        match = stored == {d: v for d, v in N.items() if v}
        print(f"  k={k} beta={cert['beta']}: stored N_d reproduced: {match}")
        if not match:
            print(f"    recomputed {dict(sorted(N.items()))}")
            print(f"    stored     {dict(sorted(stored.items()))}")
        print(f"    Q in [{float(Qlow):+.6e}, {float(Qhigh):+.6e}]  stored Q0={cert['Q0']}  "
              f"{'CONFIRMED > 0' if Qlow > 0 else 'NOT CONFIRMED'}")

    print()
    print("=" * 78)
    print("D. the five-point witness of item 4, pure integers")
    print("=" * 78)
    X = [(-1, 0, 0), (-1, 0, 1), (0, -1, 1), (0, 1, 1), (1, 0, 1)]
    cc = [-2, -2, 3, 3, -2]
    n = len(X)
    d = [[max(abs(a - b) for a, b in zip(X[i], X[j])) for j in range(n)] for i in range(n)]
    assert sum(cc) == 0
    Q0 = sum(cc[i] * cc[j] * d[i][j] for i in range(n) for j in range(n))
    print(f"  sum c_i c_j ||x_i-x_j||_inf = {Q0} (must be > 0): {'OK' if Q0 > 0 else 'FAIL'}")
    lam = 29
    pos = sum(lam * d[i][j] * cc[i] * cc[j] for i in range(n) for j in range(n)
              if i != j and cc[i] * cc[j] > 0)
    neg2 = sum(lam * d[i][j] * (-cc[i] * cc[j]) for i in range(n) for j in range(n)
               if i != j and cc[i] * cc[j] < 0)
    neg3 = sum(-cc[i] * cc[j] for i in range(n) for j in range(n)
               if i != j and cc[i] * cc[j] < 0)
    print(f"  lambda={lam}: 2^{pos} vs 2^{neg2} * 3^{neg3} -> "
          f"{'2^%d > 2^%d*3^%d  OK' % (pos, neg2, neg3) if 2 ** pos > 2 ** neg2 * 3 ** neg3 else 'FAIL'}")
    print(f"  claim text asserts 2^2204 > 2^2088 * 3^72: exponents match: "
          f"{(pos, neg2, neg3) == (2204, 2088, 72)}")
    smallest = min(l for l in range(1, 60)
                   if 2 ** (l * 76) > 2 ** (l * 72) * 3 ** 72)
    print(f"  smallest scale lambda for which the interval bound closes: {smallest}")


if __name__ == "__main__":
    main()
