"""Certificate for the full-triple floor sigma_b >= 2/25.

See research/fpbs-weakly-bernoulli-fold-seeds-have-density-at-least-2-25.md and
research/artifacts/fpbs-full-triple-fold-seed-floor-2026-09-17.md.

Random model: sigma_a, sigma_b independent uniform permutations of [n];
triple T_v = (v, sigma_a v, sigma_b v). Call v a FULL triple of I if all three
entries lie in I. For |I| = m and V subset I with |V| = f,
    P(sigma_a V subset I and sigma_b V subset I) = [(m)_f / (n)_f]^2
                                                  = [C(m,f) / C(n,f)]^2.
Union over I and V:
    P(some m-set has >= f full triples) <= C(n,m) C(m,f)^3 / C(n,f)^2.
Exponent: J(x, z) = H(x) + 3 x H(z/x) - 2 H(z), with m/n -> x, f/n -> z.

Part 1: exact certificate at (x, z) = (1/2, 21/50) with mpmath.
Part 2: exact finite-n log first moment (lgamma) at n = 10^4, 10^5, 10^6.
Part 3: optimum of x - z*(x) for this simple bound, and the sharper
        hypergeometric first moment (exact law of the full-triple count of a
        fixed set), for comparison only.
Part 4: comparison with the slot bound of fpbs-weakly-bernoulli-fold-seeds-
        have-density-floor (1/80, optimum 0.01406).
"""
from mpmath import mp, mpf, log, loggamma

mp.dps = 40


def H(p):
    p = mpf(p)
    if p <= 0 or p >= 1:
        return mpf(0)
    return -(p * log(p) + (1 - p) * log(1 - p))


def J(x, z):
    x, z = mpf(x), mpf(z)
    return H(x) + 3 * x * H(z / x) - 2 * H(z)


def lC(N, K):
    return loggamma(N + 1) - loggamma(K + 1) - loggamma(N - K + 1)


def finite_log_moment(n, m, f):
    return lC(n, m) + 3 * lC(m, f) - 2 * lC(n, f)


print("Part 1: certificate")
x0, z0 = mpf(1) / 2, mpf(21) / 50
print("  J(1/2, 21/50) =", mp.nstr(J(x0, z0), 12), "(must be < 0)")
print("  floor x - z   =", x0 - z0, "= 2/25")
# J is continuous, so it stays negative for (m/n, f/n) near (1/2, 21/50).
for dx in (mpf("1e-4"), mpf("-1e-4")):
    for dz in (mpf("1e-4"), mpf("-1e-4")):
        v = J(x0 + dx, z0 + dz)
        print("  J(1/2%+.0e, 21/50%+.0e) = %s" % (float(dx), float(dz), mp.nstr(v, 8)))
        assert v < mpf("-0.006")
print("  J < -0.006 at the corners of the box |dx|,|dz| <= 1e-4: ok")

print("Part 2: exact finite-n log first moment, m = ceil(n/2), f = ceil(21n/50)")
for n in (10**4, 10**5, 10**6):
    m = -(-n // 2)
    f = -(-21 * n // 50)
    print("  n=%d  log P-bound = %s" % (n, mp.nstr(finite_log_moment(n, m, f), 8)))


def zstar(x):
    x = mpf(x)
    lo, hi = x / 2, x * (1 - mpf(10) ** -15)
    if J(x, lo) < 0:
        return lo
    for _ in range(120):
        mid = (lo + hi) / 2
        if J(x, mid) < 0:
            hi = mid
        else:
            lo = mid
    return hi


print("Part 3: optimum of the simple bound")
best = max(((mpf(i) / 1000 - zstar(mpf(i) / 1000), mpf(i) / 1000)
            for i in range(400, 700, 2)), key=lambda t: t[0])
print("  best floor %.6f at x = %.3f" % (float(best[0]), float(best[1])))


def xh(a, b):
    a, b = mpf(a), mpf(b)
    if a <= 0 or b <= 0 or b >= a:
        return mpf(0)
    return a * H(b / a)


def Psi(x, y1, y2, z):
    # (1/n) log of C(n,m) P(|X cap sa^-1 X| = y1 n) P(|X cap sb^-1 X| = y2 n)
    # P(|J_a cap J_b| = z n); exact large deviation rate of the full-triple
    # count of a fixed set, times the number of sets.
    return (-H(x) + xh(x, y1) + xh(1 - x, x - y1) + xh(1 - x, x - y2)
            + xh(y1, z) + xh(x - y1, y2 - z))


def supPsi(x, z0, grid=41):
    best = mpf(-10)
    lo = max(0, 2 * x - 1)
    for i in range(grid + 1):
        y1 = max(lo, z0) + (x - max(lo, z0)) * i / grid
        for j in range(grid + 1):
            y2 = max(lo, z0) + (x - max(lo, z0)) * j / grid
            top = min(y1, y2)
            for k in range(11):
                z = z0 + (top - z0) * k / 10
                if y2 - z <= x - y1 + mpf(10) ** -30:
                    best = max(best, Psi(x, y1, y2, z))
    return best


mp.dps = 15
print("Part 3b: hypergeometric (sharp) first moment, comparison only")
for xv in (mpf(1) / 2, mpf("0.54")):
    lo, hi = mpf(0), xv
    for _ in range(22):
        mid = (lo + hi) / 2
        if supPsi(xv, mid) < 0:
            hi = mid
        else:
            lo = mid
    print("  x=%.2f  z0=%.5f  floor=%.5f" % (float(xv), float(hi), float(xv - hi)))

print("Part 4: slot bound of the 1/80 node, E(1/8, 4/5):")
a, e = mpf(1) / 8, mpf(4) / 5
print("  E =", mp.nstr(H(a) + 2 * a * H((1 + e) / 2) + (1 + e) * a * log(a), 8),
      " floor (1-eta)alpha/2 =", (1 - e) * a / 2)
