"""Numbers for fpbs-lossless-move-comparison-fails-marginal-transfer.

Two-path lossless comparison for an Add move S -> T = S u {t, t^-1}, t = uv:
an edge {x, xt} is declared open iff one of the N edge-disjoint S-paths
x -> x u_i -> x t is open.  Its marginal is m_N(p) = 1 - (1 - p^2)^N.
The lossless inequality (LL) would read p_c(S) <= m_N^{-1}(p_c(T)).

Run: python3 thresholds.py
"""
import math


def m(N, p):
    return 1 - (1 - p * p) ** N


def m_inv(N, q):
    # 1 - (1 - p^2)^N = q  <=>  p = sqrt(1 - (1 - q)^(1/N))
    return math.sqrt(1 - (1 - q) ** (1.0 / N))


def phi(M, p):
    # power map of fpbs-generating-set-threshold-comparison with L = 2
    return (1 - (1 - p) ** (1.0 / M)) ** 2


def phi_inv(M, q):
    return 1 - (1 - math.sqrt(q)) ** M


def bisect(f, lo, hi, it=200):
    for _ in range(it):
        mid = (lo + hi) / 2
        if f(lo) * f(mid) <= 0:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2


# Z^2 -> triangular lattice, t = e1 + e2, N = 2 edge-disjoint 2-paths, M = 2.
pc_sq = 0.5                            # Kesten 1980
pc_tri = 2 * math.sin(math.pi / 18)    # Wierman 1981
print("Z^2 -> triangular")
print("  p_c(tri)               =", pc_tri)
print("  m_2^{-1}(p_c(tri))     =", m_inv(2, pc_tri), "(LL prediction for p_c(Z^2) upper bound)")
print("  phi_2^{-1}(p_c(tri))   =", phi_inv(2, pc_tri), "(established power-map upper bound)")
print("  true p_c(Z^2)          =", pc_sq)
for p in (0.44, 0.45, 0.49):
    print("  p=%.2f  t-edge marginal m_2(p) = %.6f  > p_c(tri)? %s" % (p, m(2, p), m(2, p) > pc_tri))

# F_2 = <a,b>: T_4 -> tree of triangles (3 triangles per vertex), t = ab, N = 1.
q = bisect(lambda p: 4 * (p + p * p - p ** 3) - 1, 0.0, 1.0)
print("F_2 {a,b} -> {a,b,ab}")
print("  p_c(tree of triangles) =", q, "(root of 4(p + p^2 - p^3) = 1)")
print("  m_1^{-1}(p_c(T))       =", m_inv(1, q), ">= p_c(T_4) = 1/3 ?", m_inv(1, q) >= 1 / 3)
print("  phi_2^{-1}(p_c(T))     =", phi_inv(2, q))

# Ratio bound m_N(p) <= N M^2 phi_M(p) on (0,1].
worst = 0.0
for k in range(1, 10001):
    p = k / 10000
    for N in (1, 2, 3, 4):
        for M in (2, 3, 4):
            worst = max(worst, m(N, p) / (N * M * M * phi(M, p)))
print("max over grid of m_N(p) / (N M^2 phi_M(p)) =", worst, "(must be <= 1)")
