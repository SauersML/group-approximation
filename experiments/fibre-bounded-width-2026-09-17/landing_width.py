"""Bounded-width fibre branching calibration.

The factor B = Z^k (degree 2k) at p = 1/(2k + a + 1 + eta), a = ||A_H||.
The cluster |C| of o in B is stochastically dominated by the total progeny T
of a Galton-Watson tree: root offspring Bin(2k, p), others Bin(2k-1, p).
Hitting-time theorem: P(T = 1 + n | R = r) = (r/n) P(Bin(n(2k-1), p) = n - r).

We print, for the dominating tree:
  W  = E[min(1, p T)]  (upper bound for P(an s-edge landing set is nonempty)),
  pchi = p E[T],
  frac = share of E[T] carried by T > 2k (clusters too big to be 'contracted'),
  lower bound pchi_B >= 1/d_H at any p > p_c(G) (Theorem B).
The quantity d_H * W bounds the mean offspring of any exploration that keeps
at most one child cluster per child fibre; it tends to 0 like k^(-1/2).
"""
import numpy as np
from scipy.stats import binom

def gw(k, p, nmax):
    m = 2 * k - 1
    rs = np.arange(0, 2 * k + 1)
    pr = binom.pmf(rs, 2 * k, p)
    P = np.zeros(nmax + 2)
    P[1] = pr[0]
    for n in range(1, nmax + 1):
        r = rs[1:min(n, 2 * k) + 1]
        P[n + 1] = np.sum(pr[r] * (r / n) * binom.pmf(n - r, n * m, p))
    return P

def row(k, a, eta, dH):
    p = 1.0 / (2 * k + a + 1 + eta)
    nstar = int(np.ceil(1 / p))
    P = gw(k, p, nstar + 1)
    ns = np.arange(len(P))
    head = P[: nstar + 1]
    W = np.sum(head * np.minimum(1.0, p * ns[: nstar + 1])) + max(0.0, 1 - head.sum())
    ET = 1 + 2 * k * p / (1 - (2 * k - 1) * p)
    small = np.sum((P * ns)[: 2 * k + 1])
    return p, W, p * ET, 1 - small / ET, dH * W

if __name__ == "__main__":
    a, dH = 2 * np.sqrt(3), 4  # H = F_2 with free generators
    print("k      p         W=E[min(1,pT)]  p*E[T]   share(T>2k)  d_H*W   sqrt(k)*W")
    for k in [10, 30, 100, 300, 1000, 3000]:
        p, W, pET, fr, bound = row(k, a, 0.1, dH)
        print(f"{k:5d}  {p:.3e}  {W:.4e}      {pET:.4f}   {fr:.4f}       {bound:.4f}  {np.sqrt(k)*W:.4f}")
