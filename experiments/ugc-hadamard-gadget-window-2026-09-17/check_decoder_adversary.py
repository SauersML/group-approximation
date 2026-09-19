"""Exact check of the nearest-codeword decoder adversary of
hadamard-gadget-deletion-ratio-window, item 3:

    R*(k) <= 1 + delta_k (3 - 4/K),   delta_k = E_xi[d(xi, C)] / |P|,

C = the signed dictator patterns a -> tau chi_a(i) on the primary set P
(the first-order Reed-Muller code RM(1,k) when P contains chi_0, its
puncturing when it does not).

Adversary A (xi uniform on {-1,1}^P; (i, tau) a uniformly random nearest
signed codeword to xi; t uniform on [3/4, 1]):
  * x with m(x)/K > t has a unique closest signed primary y0 = sigma chi_p
    (Fact 6.2):  if xi_p == tau chi_p(i) ("agree") A(x) = tau x_i,
                 else ("disagree")                A(x) = sigma xi_p;
  * every other x: A(x) = tau x_i.
A is folded and A(chi_a) = xi_a (a primary has m = K, is always in the
corrected zone, and in both branches returns xi_a).

The script computes the exact joint law  w[i, tau, p, v] = Pr[(i,tau)
decoded, xi_p = v]  by enumerating all xi (uniform tie-breaking), checks
  (1) Pr[disagree_p | i] = delta_k for every i and p (equivariance),
  (2) on every length-one edge, K * Pr[A cuts it] is 1 if both endpoints
      have m <= 3K/4 and exactly 1 + delta_k (3 - 4/K) otherwise,
using that a length-one edge reads xi on at most one primary (two vertices
at distance 1 cannot be near two different signed primaries, which are at
distance >= K/2).  Floating point with tolerance 1e-9; delta_k itself is
exact (Fraction).  Runs k = 3 (both primary sets) and k = 4 (both).
"""
import sys
import itertools
import numpy as np
from fractions import Fraction


def popcount(a):
    a = a.astype(np.uint64)
    c = np.zeros(a.shape, dtype=np.int64)
    while np.any(a):
        c += (a & np.uint64(1)).astype(np.int64)
        a >>= np.uint64(1)
    return c


def run(k, first):
    K = 1 << k
    alist = list(range(first, K))
    P = len(alist)
    chi = np.array([[1 - 2 * (bin(a & i).count("1") % 2) for i in range(K)] for a in alist])  # P x K
    # joint law of (i, tau, p, xi_p)
    w = np.zeros((K, 2, P, 2))            # tau index 0 <-> +1, v index 0 <-> +1
    dist_sum = Fraction(0)
    nxi = 1 << P
    for bits in range(nxi):
        xi = np.array([1 - 2 * ((bits >> p) & 1) for p in range(P)])
        corr = xi @ chi                    # length K: sum_p xi_p chi_p(i)
        # distance to tau chi(i) is (P - tau corr_i) / 2
        cands = [(i, t) for i in range(K) for t in (0, 1) if (1 - 2 * t) * corr[i] == np.abs(corr).max()]
        d = (P - int(np.abs(corr).max())) // 2
        dist_sum += d
        for (i, t) in cands:
            for p in range(P):
                w[i, t, p, 0 if xi[p] == 1 else 1] += 1.0 / (nxi * len(cands))
    delta = dist_sum / (nxi * P)
    # (1) Pr[disagree_p | i] = delta
    for i in range(K):
        pi = w[i].sum(axis=(0, 2))[0]
        for p in range(P):
            dis = 0.0
            for t in (0, 1):
                tau = 1 - 2 * t
                agree_v = 0 if tau * chi[p, i] == 1 else 1
                dis += w[i, t, p, 1 - agree_v]
            assert abs(dis / pi - float(delta)) < 1e-9, ("not uniform", i, p, dis / pi, delta)
        assert abs(pi - 1.0 / K) < 1e-9
    # geometry
    V = np.arange(1 << K, dtype=np.int64)
    masks = [sum(1 << i for i in range(K) if chi[p, i] == -1) for p in range(P)]
    best = np.full(V.shape, -1, dtype=np.int64)
    cp = np.zeros(V.shape, dtype=np.int64)
    cs = np.zeros(V.shape, dtype=np.int64)
    for idx, mask in enumerate(masks):
        agree = K - popcount(V ^ mask)
        for sgn, m in ((1, agree), (-1, K - agree)):
            upd = m > best
            best = np.where(upd, m, best)
            cp = np.where(upd, idx, cp)
            cs = np.where(upd, sgn, cs)
    thr = 3 * K // 4
    target = 1 + float(delta) * (3 - 4 / K)

    def value(x, i, tau, l, v):
        near = best[x] >= l + 1
        agree = v == tau * chi[cp[x], i]
        xi_i = 1 - 2 * ((x >> i) & 1)
        return np.where(near & ~agree, cs[x] * v, tau * xi_i)

    worst = 0.0
    for j in range(K):
        x = V[(V >> j) & 1 == 0]
        y = x ^ (1 << j)
        nx, ny = best[x] > thr, best[y] > thr
        both = nx & ny
        assert np.all(cp[x][both] == cp[y][both]), "edge near two primaries"
        pe = np.where(nx, cp[x], cp[y])
        pr = np.zeros(x.shape)
        for i in range(K):
            for t in (0, 1):
                tau = 1 - 2 * t
                for vi, v in ((0, 1), (1, -1)):
                    wt = w[i, t, pe, vi]          # per-edge weight of this cell
                    for l in range(thr, K):
                        c = value(x, i, tau, l, v) != value(y, i, tau, l, v)
                        pr += wt * c / (K // 4)
        kp = K * pr
        near = nx | ny
        assert np.allclose(kp[~near], 1.0, atol=1e-9), "far edge not dictator-priced"
        assert np.allclose(kp[near], target, atol=1e-9), ("closed form fails", kp[near].min(), kp[near].max(), target)
        worst = max(worst, kp.max())
    print(f"k={k}, |P|={P} (a >= {first}): delta_k = {delta} = {float(delta):.6f}; "
          f"max_e K*Pr[cut] = {worst:.9f} = 1 + delta(3-4/K) = {target:.9f}")
    return delta


if __name__ == "__main__":
    ks = [int(a) for a in sys.argv[1:]] or [3, 4]
    for k in ks:
        for first in (0, 1):
            run(k, first)
    print("all checks passed")
