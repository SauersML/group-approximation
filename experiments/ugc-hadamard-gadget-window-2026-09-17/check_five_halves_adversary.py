"""Exact check of the corrected threshold adversary of
hadamard-gadget-deletion-ratio-window, item 2 (R*(k) <= 5/2 - 2^(1-k)).

Setting (HHM+15 normal form).  K = 2^k coordinates i in F_2^k, vertices
x in {-1,1}^K stored as bitmasks (bit i set  <=>  x_i = -1).  The
primaries are the characters chi_a(i) = (-1)^(a.i); both the HHM+15
Definition 2.24 set (all a, including the constant chi_0) and the
nonconstant set (a != 0, Had'_k) are checked.  sim(x, y) =
fraction of agreeing coordinates, m(x) = K * max_{y in P+-} sim(x, y).

Adversary A (random xi in {-1,1}^P, dictator i uniform in [K], t uniform on
[3/4, 1], all independent):
  * x with m(x)/K > t has a unique closest y0 = sigma chi_p (Fact 6.2);
      - if xi_p == chi_p(i) ("agree"): A(x) = x_i,
      - else ("disagree"):             A(x) = sigma xi_p;
  * every other x: A(x) = x_i.

For every length-one edge the script computes Pr[A cuts the edge] EXACTLY:
t is integrated over the K/4 intervals (l/K, (l+1)/K), l = 3K/4..K-1, each of
probability 4/K, on which the type of every vertex is constant; i runs over
[K]; and xi is summed over its values on the (at most two) primaries that the
two endpoints can read, which is exact because xi is uniform and independent.
It asserts
  (a) A(-x) = -A(x) for every x and every (i, t, xi) cell (folded),
  (b) A(chi_a) = xi_a for every a (so A is random on the generic primaries),
  (c) K * Pr[cut] <= 5/2 - 2/K on every length-one edge, with equality on
      the edges next to a primary,
  (d) K * Pr[cut] == 1 on edges whose endpoints both have m <= 3K/4, and
      K * Pr[cut] == 5/2 - 2/K on every edge with max m > 3K/4 (the closed
      form of the proof).
Runs k = 2, 3, 4 (k = 4 has 2^16 vertices and 2^19 edges) in about a minute.
"""
import sys
import numpy as np
from fractions import Fraction


def popcount(a):
    a = a.astype(np.uint64)
    c = np.zeros(a.shape, dtype=np.int64)
    while np.any(a):
        c += (a & np.uint64(1)).astype(np.int64)
        a >>= np.uint64(1)
    return c


def run(k, first=0):
    K = 1 << k
    V = np.arange(1 << K, dtype=np.int64)
    prim = []
    for a in range(first, K):
        mask = 0
        for i in range(K):
            if bin(a & i).count("1") % 2:
                mask |= 1 << i
        prim.append(mask)
    # similarity counts to +chi_a and -chi_a
    best = np.full(V.shape, -1, dtype=np.int64)
    cp = np.full(V.shape, -1, dtype=np.int64)     # index of closest primary
    cs = np.zeros(V.shape, dtype=np.int64)        # sign sigma
    for idx, mask in enumerate(prim):
        agree = K - popcount(V ^ mask)
        for sgn, m in ((1, agree), (-1, K - agree)):
            upd = m > best
            best = np.where(upd, m, best)
            cp = np.where(upd, idx, cp)
            cs = np.where(upd, sgn, cs)
    thr = 3 * K // 4
    # Fact 6.2: at most one of the 2(K-1) signed primaries has m > 3K/4
    cnt = np.zeros(V.shape, dtype=np.int64)
    for mask in prim:
        agree = K - popcount(V ^ mask)
        cnt += (agree > thr).astype(np.int64) + ((K - agree) > thr).astype(np.int64)
    assert np.all(cnt <= 1), "Fact 6.2 fails"
    chi = np.array([[1 - 2 * ((m >> i) & 1) for i in range(K)] for m in prim])  # (K-1) x K

    def xval(x, i):
        return 1 - 2 * ((x >> i) & 1)

    def value(x, i, l, xi_of):
        """A(x) on cell (i, t in (l/K,(l+1)/K)); xi_of: array of xi at cp(x)."""
        t1 = best[x] >= l + 1          # m/K > t  <=>  m >= l+1
        p = cp[x]
        agree = xi_of == chi[p, i]
        v = np.where(t1 & ~agree, cs[x] * xi_of, xval(x, i))
        return v

    full = (1 << K) - 1
    # (a) folding and (b) primaries, on every vertex and cell, xi read at cp(x)
    for i in range(K):
        for l in range(thr, K):
            for e in (1, -1):
                xi = np.full(V.shape, e)
                assert np.all(value(V, i, l, xi) == -value(V ^ full, i, l, xi)), "not folded"
        for idx, mask in enumerate(prim):
            for l in range(thr, K):
                for e in (1, -1):
                    got = value(np.array([mask]), i, l, np.array([e]))[0]
                    assert got == e, "primary not random"
    # (c), (d): exact cut probabilities on all length-one edges
    worst = Fraction(0)
    for j in range(K):
        x = V[(V >> j) & 1 == 0]
        y = x ^ (1 << j)
        cuts = np.zeros(x.shape, dtype=np.int64)
        px, py = cp[x], cp[y]
        same = px == py
        for i in range(K):
            for l in range(thr, K):
                for e1 in (1, -1):
                    for e2 in (1, -1):
                        xix = np.full(x.shape, e1)
                        xiy = np.where(same, e1, e2)
                        cuts += (value(x, i, l, xix) != value(y, i, l, xiy)).astype(np.int64)
        # Pr = cuts / (K * (K/4) * 4); K*Pr = cuts / (K/4 * 4) = cuts / K
        denom = K  # K * Pr[cut] = cuts / denom
        bound = Fraction(5, 2) - Fraction(2, K)
        mx = int(cuts.max())
        assert Fraction(mx, denom) <= bound, (k, j, mx)
        worst = max(worst, Fraction(mx, denom))
        near = np.maximum(best[x], best[y]) > thr
        assert np.all(cuts[~near] == denom), "far edge not dictator-priced"
        assert np.all(cuts[near] * 1 == bound * denom), "closed form fails"
    print(f"k={k}, primaries chi_a for a >= {first} ({len(prim)} of them): K={K}, vertices={1 << K}, max K*Pr[cut] = {worst} = 5/2 - 2/K: {worst == Fraction(5, 2) - Fraction(2, K)}")
    return worst


if __name__ == "__main__":
    ks = [int(a) for a in sys.argv[1:]] or [2, 3, 4]
    for k in ks:
        for first in (0, 1):
            run(k, first)
    print("all checks passed")
