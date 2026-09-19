"""Exact rational certificate: the critical two-point function of
X = Cay(F_r x Z, {a_i^{+-1}} u {t^{+-1},...,t^{+-k}}) beats gr^{-|x|/2}.

Proof being certified: research/fpbs-pointwise-critical-bound-fails-on-spread-products-proof.md.

Quantities (all exact rationals):
  q   = 1/(d-1), d = 2r+2k           (q <= p_c(X), path counting)
  gr  = 2r-1                         (growth rate of X)
  layered family: v_0 = 0, v_i in I_i = {i s, ..., i s + w - 1} (1 <= i <= m-1),
                  v_m = m s; all hops lie in [1, k] when w <= s and s + w - 1 <= k.
  EN  = w^(m-1) q^m
  Z_m = sum over agreement sets, computed by the 2x2 transfer matrix
        K = [[1, (w-1) q], [q, (w-1) q]] (states: agree, differ), final vector (1, q).
  LB  = EN / Z_m  <=  P_q(0 <-> m s in the fibre)  <=  tau_{p_c}^X(o, t^{m s}).
  |t^{m s}| = ceil(m s / k).

Certificate: LB^2 * gr^{ceil(m s / k)} > 1, i.e. tau_{p_c}(o, x) > gr^{-|x|/2}.
"""

from fractions import Fraction
import math
import sys


def z_m(w, q, m):
    """Exact Z_m = e_agree^T K^(m-1) g, g = (1, q)."""
    x = (w - 1) * q
    # row vector starting at state 'agree' (index 0) at site 0
    a, b = Fraction(1), Fraction(0)  # weights of paths ending at site i in agree/differ
    # step from site i-1 to site i for i = 1..m-1, site i gets vertex weight
    for _ in range(m - 1):
        a, b = a * 1 + b * q, a * x + b * x
    # last step to site m, which is forced to 'agree' (vertex weight 1)
    return a * 1 + b * q


def certify(r, k, w, s, m, j=2):
    """Certify tau_{p_c}(o, t^{m s}) > gr^{-|x|/j} exactly (alpha = 1/j)."""
    assert r >= 2 and 1 <= w <= s and s + w - 1 <= k and m >= 2 and j >= 1
    q = Fraction(1, 2 * r + 2 * k - 1)
    gr = 2 * r - 1
    en = Fraction(w) ** (m - 1) * q ** m
    z = z_m(w, q, m)
    lb = en / z
    length = -(-m * s // k)  # ceil
    ratio = lb ** j * Fraction(gr) ** length  # > 1 means LB > gr^{-|x|/j}
    return {
        "r": r, "k": k, "w": w, "s": s, "m": m, "alpha": f"1/{j}",
        "|x|": length,
        "log10_LB": math.log10(lb.numerator) - math.log10(lb.denominator),
        "log10_bound": -length / j * math.log10(gr),
        "Z_m": float(z),
        "violation": ratio > 1,
        "log10_ratio": math.log10(ratio.numerator) - math.log10(ratio.denominator),
    }


def check_clean_bound(D, k, n):
    """Check the ray bound (proof file, Section 5) exactly.  Here D = |S_H| is the
    size of the generating set of the first factor (D = 2r for the free basis of
    F_r), k is even, 2 <= D <= 2k, q = 1/(D+2k-1), w = s = k/2, m = 2n.  Checks
    Z_m <= (1+q)^(m-1) and LB >= q (5/48)^(m-1) >= q 100^(-n)."""
    assert k % 2 == 0 and k >= 2 and 2 <= D <= 2 * k and n >= 1
    q = Fraction(1, D + 2 * k - 1)
    w = k // 2
    m = 2 * n
    z = z_m(w, q, m)
    lb = Fraction(w) ** (m - 1) * q ** m / z
    return (z <= (1 + q) ** (m - 1)
            and lb >= q * Fraction(5, 48) ** (m - 1)
            and lb >= q * Fraction(1, 100) ** n)


def main():
    if len(sys.argv) in (6, 7):
        print(certify(*map(int, sys.argv[1:])))
        return
    ok = all(check_clean_bound(D, k, n)
             for k in (2, 4, 10, 12, 20, 50, 200)
             for D in (2, 4, 6, 10, 20, 26, 80, 400) if D <= 2 * k
             for n in (1, 2, 3, 5, 10, 20))
    print("ray bound tau_pc(o,t^{kn}) >= 100^{-n}/(D+2k-1) on sample grid:", ok)
    # Instances quoted in the proof file (Section 6).  The first line is a
    # recorded near-miss: at r = 120 the per-layer margin is positive but too
    # small to beat the 2 log w prefactor loss at m = 60.
    for params in [
        (120, 20000, 8000, 12001, 60),
        (150, 20000, 8000, 12000, 100),
        (500, 10000, 4000, 6001, 40),
        (500, 10000, 4000, 6001, 60),
        (2000, 100000, 40000, 60001, 30),
        (100000, 2000000, 700000, 1300000, 80, 4),
    ]:
        print(certify(*params))


if __name__ == "__main__":
    main()
