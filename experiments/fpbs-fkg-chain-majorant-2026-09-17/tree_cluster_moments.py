"""Harris-FKG chain majorant versus the true chain sum on the 3-regular tree.

On T_3 at p < p_c = 1/2 the cluster of the root is a Galton-Watson tree
(root offspring Bin(3,p), every other vertex Bin(2,p)).  The exact
cluster-size law comes from Lagrange inversion: a child subtree has total
progeny n with probability (1/n) P(Bin(2n,p) = n-1).

We compare
  M_m = E|K|^m, the Harris majorant of the m-chain sum (for N containing o
        the majorant E|K|^(m-1)|K cap N| is at least E|K|^(m-1)),
with the true chain sum
  sum_{x_1..x_m} prod_i tau(x_{i-1},x_i) = chi^m,
which holds exactly by transitivity, since sum_x tau(y,x) = chi for every y.

Output: m, M_m^(1/m)/chi, and the trivial lower bound m p / chi, which comes
from P(|K| > m) >= p^m.  The lower bound is an under-estimate for the ratio
because the bound (E|K|^m)^(1/m) >= m p ignores chi.
"""
from math import comb, log, exp


def cluster_law(p, nmax):
    q = 1 - p
    c = [0.0] * (nmax + 1)
    for n in range(1, nmax + 1):
        k = n - 1
        lp = log(comb(2 * n, k)) + k * log(p) + (2 * n - k) * log(q)
        c[n] = exp(lp) / n

    def conv(a, b):
        r = [0.0] * (nmax + 1)
        for i, ai in enumerate(a):
            if ai == 0.0:
                continue
            for j in range(0, nmax + 1 - i):
                r[i + j] += ai * b[j]
        return r

    powers = [[1.0] + [0.0] * nmax]
    for _ in range(3):
        powers.append(conv(powers[-1], c))
    law = [0.0] * (nmax + 1)
    for x in range(4):
        w = comb(3, x) * p ** x * q ** (3 - x)
        for n in range(nmax):
            law[n + 1] += w * powers[x][n]
    return law


if __name__ == "__main__":
    for p in (0.2, 0.35, 0.45):
        nmax = 1500
        law = cluster_law(p, nmax)
        mass = sum(law)
        chi_exact = 1 + 3 * p / (1 - 2 * p)
        chi_num = sum(n * w for n, w in enumerate(law))
        print(f"p={p}: mass={mass:.12f} chi_num={chi_num:.10f} "
              f"chi_exact={chi_exact:.10f}")
        for m in (1, 2, 4, 8, 12, 16, 20):
            Mm = sum(n ** m * w for n, w in enumerate(law))
            print(f"  m={m:2d}  (E|K|^m)^(1/m)/chi = {Mm ** (1 / m) / chi_exact:9.4f}"
                  f"   lower bound m*p/chi = {m * p / chi_exact:7.4f}")
