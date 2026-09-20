"""Brute-force check of the half-cube bubble adversary at k = 3, from the
definition, with no closed-form pricing.

The randomness is i (uniform coordinate), tau (uniform sign), and B (uniform
subset of characters), all independent; xi_a = tau chi_a(i) for a not in B
and -tau chi_a(i) for a in B, so xi is uniform.
  e_a(x) = (K - x_i chi_a(i) W_a(x)) / 2,
  H_t(x) = -tau x_i  if min_{a in B} e_a(x) <= t,  else  tau x_i.
Checks, for every t in [0, K/2):
  1. folding: H_t(-x) = -H_t(x) for every outcome;
  2. pins: H_t(sigma chi_a) = sigma xi_a for every outcome;
  3. for every x and edge direction j, K * Pr[H_t(x) != H_t(x^j)] equals the
     closed-form price of halfcube_price.prices.
"""
import itertools
from fractions import Fraction
from halfcube_price import chars, walsh, prices

k = 3
K = 1 << k
ch = chars(k)
subsets = [frozenset(a for a in range(K) if m >> a & 1) for m in range(1 << K)]


def H(x, W, i, tau, B, t):
    flip = any((K - x[i] * ch[a][i] * W[a]) // 2 <= t for a in B)
    return -tau * x[i] if flip else tau * x[i]


pts = list(itertools.product((1, -1), repeat=K))
Wtab = {x: walsh(x, ch) for x in pts}
bad = 0
for t in range(K // 2):
    for x in pts:
        nx = tuple(-v for v in x)
        for i in range(K):
            for tau in (1, -1):
                for B in subsets:
                    if H(nx, Wtab[nx], i, tau, B, t) != -H(x, Wtab[x], i, tau, B, t):
                        bad += 1
    for a in range(K):
        for sg in (1, -1):
            x = tuple(sg * c for c in ch[a])
            for i in range(K):
                for tau in (1, -1):
                    for B in subsets:
                        xi = -tau * ch[a][i] if a in B else tau * ch[a][i]
                        if H(x, Wtab[x], i, tau, B, t) != sg * xi:
                            bad += 1
print("folding and pin violations:", bad)
mism = 0
for x in pts[: len(pts) // 2]:
    for j in range(K):
        y = list(x)
        y[j] = -y[j]
        y = tuple(y)
        closed = prices(list(x), j, k, ch)
        for t in range(K // 2):
            cnt = sum(H(x, Wtab[x], i, tau, B, t) != H(y, Wtab[y], i, tau, B, t)
                      for i in range(K) for tau in (1, -1) for B in subsets)
            brute = Fraction(K * cnt, K * 2 * len(subsets))
            if brute != closed[t]:
                mism += 1
print("closed-form price mismatches:", mism)
