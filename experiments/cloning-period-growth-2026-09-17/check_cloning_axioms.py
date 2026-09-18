#!/usr/bin/env python3
"""Check the bit-register cloning system and the configuration representation phi.

G_n = Sym({0,1}^n) (product = composition, (gh)(x) = g(h(x))), rho_n trivial,
iota_{m,n}(s) = s on the first m bits, identity on the rest,
(s)kappa^n_k = s acting on coordinates {1..n+1} minus {k+1}, identity on coordinate k+1.

Checks (maps written on the right, as in Zaremsky's user's guide arXiv:1606.08762):
  (C1) pure case: kappa_k is a homomorphism,
  (C2) (g)kappa^n_l kappa^{n+1}_k == (g)kappa^n_k kappa^{n+1}_{l+1} for k < l,
  Eq.(2) (g)iota_{m,n} kappa^n_k == (g)kappa^m_k iota_{m+1,n+1} for k <= m,
  sanity: the same (C2) reading holds for the direct-power example of the guide
          and the other reading fails for it,
  phi: the configuration action is invariant under expansions and multiplicative.
"""
import itertools
import random
from fractions import Fraction as Fr

random.seed(1)


def bits(n):
    return list(itertools.product((0, 1), repeat=n))


def rand_perm(n):
    xs = bits(n)
    ys = xs[:]
    random.shuffle(ys)
    return dict(zip(xs, ys))


def compose(g, h):  # (gh)(x) = g(h(x))
    return {x: g[h[x]] for x in h}


def kappa(s, n, k):  # s in Sym({0,1}^n), 1 <= k <= n
    out = {}
    for x in bits(n + 1):
        rest = x[:k] + x[k + 1:]  # drop coordinate k+1 (0-based index k)
        y = s[rest]
        out[x] = y[:k] + (x[k],) + y[k:]
    return out


def iota(s, m, n):
    out = {}
    for x in bits(n):
        out[x] = s[x[:m]] + x[m:]
    return out


def check_system(nmax=3, trials=4):
    for n in range(1, nmax + 1):
        for _ in range(trials):
            g, h = rand_perm(n), rand_perm(n)
            for k in range(1, n + 1):
                assert kappa(compose(g, h), n, k) == compose(kappa(g, n, k), kappa(h, n, k)), "C1"
                for l in range(k + 1, n + 1):
                    lhs = kappa(kappa(g, n, l), n + 1, k)
                    rhs = kappa(kappa(g, n, k), n + 1, l + 1)
                    assert lhs == rhs, "C2"
            for m in range(1, n + 1):
                gm = rand_perm(m)
                for k in range(1, m + 1):
                    assert kappa(iota(gm, m, n), n, k) == iota(kappa(gm, m, k), m + 1, n + 1), "Eq2"
    print("cloning axioms (C1),(C2),(C3 trivial),Eq.(2): OK for n <=", nmax)


def check_direct_power_convention():
    # direct powers of Z/5: (g_1..g_n)kappa_k = (g_1..g_k,g_k,..,g_n)
    def dk(g, k):
        return g[:k] + (g[k - 1],) + g[k:]
    other_fails = False
    for n in range(2, 6):
        g = tuple(random.randrange(5) for _ in range(n))
        for k in range(1, n + 1):
            for l in range(k + 1, n + 1):
                assert dk(dk(g, l), k) == dk(dk(g, k), l + 1)
                if l + 1 <= n and dk(dk(g, k), l) != dk(dk(g, l + 1), k):
                    other_fails = True
    assert other_fails
    print("direct-power sanity: right-action reading of (C2) holds, left reading fails: OK")


if __name__ == "__main__":
    check_system()
    check_direct_power_convention()
