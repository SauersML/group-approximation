#!/usr/bin/env python3
"""Exact checks for research/artifacts/fpbs-tree-relative-cogrowth-2026-09-16.md.

On the 6-regular tree T = Cay(F_3, {a,b,c}^{+-}) with q = 5, and a normal
subgroup N with quotient Q, the relative susceptibility is
chi^N_p = sum_n f_n p^n, where f_n is the number of reduced words of length n
lying in N.  The artifact proves the identity of power series

    sum_n f_n s^n = (1 - s^2)/(1 + q s^2) * sum_m g_m z^m,   z = s/(1 + q s^2),

where g_m = (A^m)(e,e) counts closed label walks of length m on Q.

Checks:
  (A) N = [F_3,F_3], Q = Z^3: brute-force f_n (dynamic programming over
      exponent sums) versus the series coefficients, n <= NMAX_Z3.
  (B) N = normal closure of c, Q = F_2 with labels {a,b}^{+-} and two loops:
      brute-force f_n (dynamic programming over the F_2 image) versus the
      series coefficients, n <= NMAX_F2.
  (C) Numerical constants: Watson's value G_{Z^3}(1), chi^N_{1/5} = (4/5) G,
      the threshold s_N for case (B), coefficient ratios of the series, and
      the value 9/5 of formula (7.1) at p = 1/5 in case (B), summing the
      exact coefficients h_n for n <= NSERIES.
Single-threaded, exact integer arithmetic for (A) and (B).
"""
import math
from math import comb

import numpy as np

Q_BRANCH = 5          # q = 2d - 1 with d = 3
NMAX_Z3 = 22          # int64 safe: 6 * 5^21 < 2^63
NMAX_F2 = 14
NSERIES = 240


def series_from_closed_walks(g, nmax, q=Q_BRANCH):
    """Coefficients of (1-s^2)/(1+q s^2) * sum_m g_m (s/(1+q s^2))^m."""
    out = [0] * (nmax + 1)
    # sum_m g_m s^m (1+q s^2)^(-m-1), then multiply by (1 - s^2)
    tmp = [0] * (nmax + 1)
    for m, gm in enumerate(g):
        if m > nmax or gm == 0:
            continue
        # (1+q s^2)^(-(m+1)) = sum_i (-1)^i C(m+i, i) q^i s^(2i)
        i = 0
        while m + 2 * i <= nmax:
            tmp[m + 2 * i] += gm * (-1) ** i * comb(m + i, i) * q ** i
            i += 1
    for n in range(nmax + 1):
        out[n] = tmp[n] - (tmp[n - 2] if n >= 2 else 0)
    return out


# ---------------------------------------------------------------- (A) Z^3
def closed_walks_z3(mmax):
    g = [0] * (mmax + 1)
    for m in range(0, mmax + 1, 2):
        k = m // 2
        tot = 0
        for i in range(k + 1):
            for j in range(k - i + 1):
                l = k - i - j
                tot += math.factorial(m) // (math.factorial(i) ** 2 * math.factorial(j) ** 2 * math.factorial(l) ** 2)
        g[m] = tot
    return g


def brute_force_commutator_f3(nmax):
    """f_n = # reduced words of length n in F_3 with all exponent sums zero."""
    size = 2 * nmax + 3
    c = nmax + 1
    letters = [(0, +1), (0, -1), (1, +1), (1, -1), (2, +1), (2, -1)]
    inv = {0: 1, 1: 0, 2: 3, 3: 2, 4: 5, 5: 4}
    state = np.zeros((6, size, size, size), dtype=np.int64)
    for li, (ax, sg) in enumerate(letters):
        idx = [c, c, c]
        idx[ax] += sg
        state[li, idx[0], idx[1], idx[2]] = 1
    f = [1, 0]
    for n in range(2, nmax + 1):
        new = np.zeros_like(state)
        for lj, (ax, sg) in enumerate(letters):
            acc = np.zeros(state.shape[1:], dtype=np.int64)
            for li in range(6):
                if li != inv[lj]:
                    acc += state[li]
            new[lj] = np.roll(acc, sg, axis=ax)
        state = new
        f.append(int(state[:, c, c, c].sum()))
    return f


# ---------------------------------------------------------------- (B) F_2
def closed_walks_lazy_f2(mmax):
    """g_m = ((2I + A_{T_4})^m)(e,e)."""
    t = [0] * (mmax + 1)  # closed walks on the 4-regular tree
    dist = {0: 1}
    t[0] = 1
    for j in range(1, mmax + 1):
        nd = {}
        for d, cnt in dist.items():
            if d == 0:
                nd[1] = nd.get(1, 0) + 4 * cnt
            else:
                nd[d - 1] = nd.get(d - 1, 0) + cnt
                nd[d + 1] = nd.get(d + 1, 0) + 3 * cnt
        dist = nd
        t[j] = dist.get(0, 0)
    return [sum(comb(m, j) * 2 ** (m - j) * t[j] for j in range(m + 1)) for m in range(mmax + 1)]


def brute_force_normal_closure_c(nmax):
    """f_n = # reduced words of length n in F_3 whose image in F_2 = <a,b> is trivial."""
    # letters: 0=a,1=A,2=b,3=B,4=c,5=C ; F_2 image stored as tuple of letters in {0,1,2,3}
    inv = {0: 1, 1: 0, 2: 3, 3: 2, 4: 5, 5: 4}
    f = [1]
    layer = {}
    for li in range(6):
        img = (li,) if li < 4 else ()
        layer[(img, li)] = layer.get((img, li), 0) + 1
    f.append(sum(v for (img, _), v in layer.items() if img == ()))
    for n in range(2, nmax + 1):
        new = {}
        remaining = nmax - n
        for (img, last), cnt in layer.items():
            for lj in range(6):
                if lj == inv[last]:
                    continue
                if lj < 4:
                    if img and img[-1] == inv[lj]:
                        nimg = img[:-1]
                    else:
                        nimg = img + (lj,)
                else:
                    nimg = img
                if len(nimg) > remaining:
                    continue  # can never return to the identity
                key = (nimg, lj)
                new[key] = new.get(key, 0) + cnt
        layer = new
        f.append(sum(v for (img, _), v in layer.items() if img == ()))
    return f


def main():
    print("(A) N = [F_3,F_3], Q = Z^3")
    gz = closed_walks_z3(NMAX_Z3)
    fz = brute_force_commutator_f3(NMAX_Z3)
    hz = series_from_closed_walks(gz, NMAX_Z3)
    print("  brute f_n :", fz)
    print("  series    :", hz)
    okA = fz == hz
    print("  identity holds for n <=", NMAX_Z3, ":", okA)

    print("(B) N = <<c>>, Q = F_2 with two loops")
    gf = closed_walks_lazy_f2(NMAX_F2)
    ff = brute_force_normal_closure_c(NMAX_F2)
    hf = series_from_closed_walks(gf, NMAX_F2)
    print("  brute f_n :", ff)
    print("  series    :", hf)
    okB = ff == hf
    print("  identity holds for n <=", NMAX_F2, ":", okB)

    print("(C) constants")
    G = math.sqrt(6) / (32 * math.pi ** 3) * math.gamma(1 / 24) * math.gamma(5 / 24) \
        * math.gamma(7 / 24) * math.gamma(11 / 24)
    print("  Watson G_Z3(1)            = %.9f" % G)
    print("  Polya return probability  = %.9f" % (1 - 1 / G))
    print("  chi^N_(1/5) = (4/5) G     = %.9f" % (0.8 * G))
    partial = sum(fz[n] * 0.2 ** n for n in range(NMAX_Z3 + 1))
    print("  partial sum n<=%d of f_n 5^-n = %.6f (increasing to the value above)" % (NMAX_Z3, partial))
    q = Q_BRANCH
    rho = 1 / 3 + math.sqrt(3) / 3
    sN = ((q + 1) * rho - math.sqrt((q + 1) ** 2 * rho ** 2 - 4 * q)) / (2 * q)
    print("  case (B): rho_Q = %.9f, s_N = %.9f, 1/s_N = %.6f" % (rho, sN, 1 / sN))
    gbig = closed_walks_lazy_f2(NSERIES)
    hbig = series_from_closed_walks(gbig, NSERIES)
    print("  case (B): all series coefficients nonnegative:", all(x >= 0 for x in hbig))
    for n in (60, 120, 180, NSERIES - 1):
        r = (hbig[n + 1] / hbig[n - 1]) ** 0.5
        print("    n=%3d  sqrt(h_(n+1)/h_(n-1)) = %.6f" % (n, r))
    # analytic value at p = p_c(T) = 1/5, formula (7.1): (4/5) (3/2) G_nu(1) = 9/5
    val = sum(float(hbig[n]) * 0.2 ** n for n in range(NSERIES + 1))
    tail_bound = float(hbig[NSERIES]) * 0.2 ** NSERIES
    print("  case (B): sum_(n<=%d) h_n 5^-n = %.9f  (formula (7.1): 9/5 = 1.8; last term %.2e)"
          % (NSERIES, val, tail_bound))
    okC = abs(val - 1.8) < 1e-6
    phiN = (1 - sN ** 2) / (1 + q * sN ** 2)
    sN_closed = (2 + 2 * math.sqrt(3) - math.sqrt(8 * math.sqrt(3) - 4)) / 10
    print("  case (B): closed form s_N = %.11f, phi(s_N) = %.11f, chi^N_(s_N) = phi(s_N)(3+sqrt3) = %.11f"
          % (sN_closed, phiN, phiN * (3 + math.sqrt(3))))
    okC = okC and abs(sN - sN_closed) < 1e-12
    gzb = closed_walks_z3(120)
    hzb = series_from_closed_walks(gzb, 120)
    for n in (40, 80, 118):
        r = (hzb[n + 2] / hzb[n]) ** 0.5
        print("  case (A): n=%3d  sqrt(h_(n+2)/h_n) = %.6f  (limit 5)" % (n, r))
    print("ALL EXACT CHECKS PASSED" if (okA and okB) else "EXACT CHECK FAILED")
    print("NUMERICAL CHECK OF (7.1) IN CASE (B) PASSED" if okC else "NUMERICAL CHECK OF (7.1) FAILED")


if __name__ == "__main__":
    main()
