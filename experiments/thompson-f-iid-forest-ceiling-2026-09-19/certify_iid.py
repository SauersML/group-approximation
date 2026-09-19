#!/usr/bin/env python3
"""Rigorous lower bound ||K|| >= J(alpha, beta) for explicit integer size laws (exact arithmetic).

Theorem used (thompson-f-norm-bound-from-iid-size-laws-proof, steps 1-4): for nonnegative integer
weights alpha_k, beta_k (k = 1..N) with alpha_1 > 0, a = sum alpha, b = sum beta,
    ||x0 + x0^-1 + x1 + x1^-1||  >=  J = 2 S1^2/(a b) + 2 S2/(b sqrt a),
    S1 = sum_k sqrt(alpha_k beta_k),   S2 = sum_{j<=N} sqrt(beta_j c_j),   c = alpha * beta.

Everything here is exact integer / Fraction arithmetic:
  * the laws are built in floating point from spline coefficients (provenance is irrelevant to
    validity) and then frozen as integers;
  * c = alpha * beta is computed exactly by number-theoretic transforms modulo four NTT primes
    and CRT (every c_j is < the product of the primes, which is asserted); the result is
    cross-checked by the polynomial identity c(x) = alpha(x) beta(x) at x = 1, x = -1 exactly and
    at three pseudo-random points modulo the prime 2^61 - 1;
  * S1, S2 are bounded below by sums of floor square roots (math.isqrt at scale 2^E), sqrt(a)
    above by isqrt(a) + 1, so J_lo <= J exactly.
Usage: certify_iid.py K N coeffs.npy target_num target_den
"""
import sys
import hashlib
import math
import random
from fractions import Fraction
import numpy as np

SCALE_BITS = 40
PRIMES = [(998244353, 3), (469762049, 3), (167772161, 3), (754974721, 11)]


def build_laws(K, N, z):
    from spline_opt import basis, laws_from
    a, b = laws_from(z, basis(N, K))
    al = np.floor(a * a * 2.0 ** SCALE_BITS).astype(np.int64)
    be = np.floor(b * b * 2.0 ** SCALE_BITS).astype(np.int64)
    return al, be


def ntt(x, p, g, inverse=False):
    n = len(x)
    lg = n.bit_length() - 1
    rev = np.zeros(n, dtype=np.int64)
    for bit in range(lg):
        rev |= ((np.arange(n) >> bit) & 1) << (lg - 1 - bit)
    A = x[rev].copy()
    length = 2
    while length <= n:
        half = length // 2
        w = pow(g, (p - 1) // length, p)
        if inverse:
            w = pow(w, p - 2, p)
        tw = np.ones(half, dtype=np.int64)
        m = 1
        while m < half:
            wm = pow(w, m, p)
            tw[m:2 * m] = tw[:m] * wm % p
            m *= 2
        A = A.reshape(-1, length)
        u = A[:, :half].copy()
        v = A[:, half:] * tw % p
        A[:, :half] = (u + v) % p
        A[:, half:] = (u - v) % p
        A = A.reshape(-1)
        length *= 2
    if inverse:
        A = A * pow(n, p - 2, p) % p
    return A


def exact_conv(al, be):
    """Exact integer convolution, returned as a list of Python ints (full length)."""
    L = len(al) + len(be) - 1
    n = 1
    while n < L:
        n *= 2
    res = []
    for p, g in PRIMES:
        assert (p - 1) % n == 0, "transform length not supported by prime"
        fa = np.zeros(n, dtype=np.int64); fa[:len(al)] = al % p
        fb = np.zeros(n, dtype=np.int64); fb[:len(be)] = be % p
        prod = ntt(fa, p, g) * ntt(fb, p, g) % p
        res.append(ntt(prod, p, g, inverse=True)[:L])
    # Garner / CRT
    Mtot = 1
    for p, _ in PRIMES:
        Mtot *= p
    bound = (max(int(al.max()), 1) * max(int(be.max()), 1)) * min(len(al), len(be))
    assert bound < Mtot, "CRT modulus too small"
    out = [0] * L
    mods = [p for p, _ in PRIMES]
    coef = []
    for i, p in enumerate(mods):
        Mi = Mtot // p
        coef.append(Mi * pow(Mi % p, p - 2, p))
    cols = [r.tolist() for r in res]
    for j in range(L):
        v = 0
        for i in range(len(mods)):
            v += cols[i][j] * coef[i]
        out[j] = v % Mtot
    return out


def poly_eval_mod(coeffs, x, q):
    v = 0
    for c in reversed(coeffs):
        v = (v * x + c) % q
    return v


def main():
    K, N = int(sys.argv[1]), int(sys.argv[2])
    z = np.load(sys.argv[3])
    target = Fraction(int(sys.argv[4]), int(sys.argv[5]))
    al, be = build_laws(K, N, z)
    assert al.min() >= 0 and be.min() >= 0 and al[0] > 0 and be.sum() > 0
    h = hashlib.sha256(al.tobytes() + be.tobytes()).hexdigest()
    alL, beL = [int(v) for v in al], [int(v) for v in be]
    print(f"N={N} K={K} scale=2^{SCALE_BITS}  sha256(alpha|beta int64)={h}", flush=True)
    c = exact_conv(al, be)
    # identity checks c(x) = alpha(x) beta(x): polynomials indexed from size 1, so
    # index j of c corresponds to size j + 2.
    assert sum(c) == sum(alL) * sum(beL)
    alt = lambda seq: sum(v if i % 2 == 0 else -v for i, v in enumerate(seq))
    assert alt(c) == alt(alL) * alt(beL)
    q = (1 << 61) - 1
    rng = random.Random(20260919)
    for _ in range(3):
        x = rng.randrange(2, q - 1)
        assert poly_eval_mod(c, x, q) == poly_eval_mod(alL, x, q) * poly_eval_mod(beL, x, q) % q
    # floating cross-check
    from scipy.signal import fftconvolve
    cf = fftconvolve(al.astype(float), be.astype(float))
    big = cf > 1e-6 * cf.max()
    cex = np.array([float(v) for v in c])
    assert np.max(np.abs(cex[big] - cf[big]) / cf[big]) < 1e-6
    print("exact convolution: CRT bound, x=1, x=-1, 3 random points mod 2^61-1, float cross-check OK",
          flush=True)
    E = 64
    S1 = sum(math.isqrt((alL[k] * beL[k]) << (2 * E)) for k in range(N))
    # size j (2..N) of the convolution sits at c[j-2]; beta_j at beL[j-1]
    S2 = sum(math.isqrt((beL[j - 1] * c[j - 2]) << (2 * E)) for j in range(2, N + 1))
    a, b = sum(alL), sum(beL)
    sa_hi = (math.isqrt(a << (2 * E)) + 1)
    # S1_true >= S1/2^E, S2_true >= S2/2^E, sqrt(a) <= sa_hi/2^E
    J_lo = Fraction(2 * S1 * S1, (a * b) << (2 * E)) + Fraction(2 * S2, b * sa_hi)
    print(f"J_lo = {float(J_lo):.10f}   ||P|| >= J_lo/4 = {float(J_lo/4):.10f}")
    ok = J_lo / 4 > target
    print(f"J_lo/4 > {target.numerator}/{target.denominator} : {ok}")
    num, den = J_lo.numerator, J_lo.denominator
    print(f"J_lo digits: numerator {len(str(num))}, denominator {len(str(den))}")
    assert ok


if __name__ == "__main__":
    main()
