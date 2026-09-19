"""Exact spectral check for schatten-p-ratio-data-defeat-tensor-replica-amplification.

For the two families of eigenvalue data in the claim, compute EXACTLY (finite binomial sums,
truncated only where binomial mass < 1e-18) the normalized lengths of the n-fold tensor replica
for a geometric grid of degrees n, and report:
  * the unamplified Schatten-p ratio  L_p(nu)/L_p(mu)   (should tend to 0 in m),
  * min over grid n with L_p(mu^n) >= c of L_p(nu^n)    (should stay bounded below),
  * min over grid n of op, HS and rank ratios            (should stay bounded below).
Both data families are conjugation invariant, so every tensor word of degree n has
spectral measure mu^{*n}, nu^{*n}.
"""
import math
import numpy as np


def binom_pmf(n, q):
    k = np.arange(n + 1)
    if q <= 0:
        out = np.zeros(n + 1); out[0] = 1.0; return out
    if q >= 1:
        out = np.zeros(n + 1); out[-1] = 1.0; return out
    lg = (math.lgamma(n + 1) - np.array([math.lgamma(i + 1) for i in k])
          - np.array([math.lgamma(n - i + 1) for i in k]))
    return np.exp(lg + k * math.log(q) + (n - k) * math.log1p(-q))


def walk_flip_measure(n, theta, rho):
    """n-fold convolution of (1-rho)(d_{e^{i theta}}+d_{e^{-i theta}})/2 + rho d_{-1}.
    Atoms sit at theta*j + pi*b (j = net step count, b = flip parity).  The joint law of
    (j, b) is read off exactly from the generating functions
    (+-rho + (1-rho)(z+1/z)/2)^n by an FFT of size > 2n+1.  Returns (angles, weights)."""
    size = 1 << (2 * n + 2).bit_length()
    z = np.exp(2j * math.pi * np.arange(size) / size)
    base = (1 - rho) * (z + 1 / z) / 2
    cp = np.fft.fft((rho + base) ** n).real / size   # coefficients of z^j, index j mod size
    cm = np.fft.fft((-rho + base) ** n).real / size
    # np.fft.fft(values at z_k) / size gives coefficient of z^{-j}; the law is symmetric in j.
    j = np.arange(-n, n + 1)
    even = np.clip((cp[j % size] + cm[j % size]) / 2, 0, None)
    odd = np.clip((cp[j % size] - cm[j % size]) / 2, 0, None)
    angs = np.concatenate([theta * j, theta * j + math.pi])
    wts = np.concatenate([even, odd])
    return angs, wts / wts.sum()


def lengths(angs, wts, p, one_tol=1e-12):
    z = np.abs(np.exp(1j * angs) - 1.0)
    keep = wts > 1e-18
    Lp = (wts * z ** p).sum() ** (1.0 / p)
    hs = math.sqrt((wts * z ** 2).sum())
    op = z[keep].max()
    rk = wts[z > one_tol].sum()
    return Lp, hs, op, rk


def grid(nmax):
    g = sorted(set(int(round(1.3 ** k)) for k in range(0, int(math.log(nmax, 1.3)) + 2)))
    return [n for n in g if 1 <= n <= nmax]


def family(p, m):
    """Return (a-data, relator-data) as (theta, rho) pairs."""
    # Power-law instance of the conditions (S>) / (S<) of the claim.
    if p > 2:
        b = (0.5 - 1.0 / p) / 2
        eta, eps, rho = 1.0 / m, m ** (-1.0 / p - b), m ** (-1.0 - b)
        return ("flip", eta), ("walkflip", eps, rho)
    b = (2.0 - p) / (2 * p)
    x = 1.0 / m
    y = x * m ** (-b)
    rho = y ** p
    return ("walk", x), ("walkflip", y, rho)


def measure(spec, n):
    if spec[0] == "flip":
        return walk_flip_measure(n, 0.0, spec[1])
    if spec[0] == "walk":
        return walk_flip_measure(n, spec[1], 0.0)
    return walk_flip_measure(n, spec[1], spec[2])


def run(p, m, c=1.0, nmax=None):
    A, N = family(p, m)
    if nmax is None:
        nmax = 40 * m if p > 2 else 12 * m * m
    ratio0 = lengths(*measure(N, 1), p)[0] / lengths(*measure(A, 1), p)[0]
    best_rel = float("inf"); first_n = None
    rmin = {"op": 9, "hs": 9, "rk": 9}
    for n in grid(nmax):
        la = lengths(*measure(A, n), p)
        lr = lengths(*measure(N, n), p)
        if la[0] >= c:
            best_rel = min(best_rel, lr[0])
            first_n = first_n or n
        rmin["hs"] = min(rmin["hs"], lr[1] / la[1])
        rmin["op"] = min(rmin["op"], lr[2] / la[2])
        rmin["rk"] = min(rmin["rk"], lr[3] / la[3])
    return ratio0, first_n, best_rel, rmin


if __name__ == "__main__":
    for p in (1.0, 1.5, 3.0, 4.0):
        ms = (20, 40, 80) if p < 2 else (100, 1000, 10000)
        for m in ms:
            r0, n0, br, rm = run(p, m)
            print(f"p={p} m={m}: Lp-ratio(n=1)={r0:.4f}  first n with Lp(a)>=1: {n0}  "
                  f"min Lp(rel) there={br:.4f}  min ratios op={rm['op']:.3f} "
                  f"hs={rm['hs']:.3f} rank={rm['rk']:.3f}")
