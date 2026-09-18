#!/usr/bin/env python3
"""Upper bound on the spectral gap of the folded DKKMS host (TR16-198 Sec 4.2).

Companion to research/folded-dkkms-host-gap-vanishes-as-l-grows.md.

Part (a)  exact Gaussian-binomial check of the rank-drop lemma: for a uniform
          (l-1)-subspace L' of F_2^N and a surjection T: F_2^N -> F_2^2,
          P(rank T(L') <= 1) <= 3 * 2^(1-l).
Part (b)  the closed-form bound rho(l, k) of Theorem F at the DKKMS smoothing
          beta = ln ln k / k, and the least l beyond which gate (G) is vacuous
          for given X(delta) * eta'.
Part (c)  (optional, slow: pass --instance) on the small sparse instance of
          experiments/ugc-akkstv-regularize-2026-09-17, compute the exact
          canonical folded gap lambda_2 together with the exact test-function
          bound 1 - sqrt(1 - rho_exact) of the frozen-triple statistic, and
          check lambda_2 <= 1 - sqrt(1 - rho_exact), and the class invariance
          of the frozen-triple set.
"""
import math
import os
import random
import sys
from collections import defaultdict
from fractions import Fraction


def gauss_binom(n, r):
    """Number of r-dimensional subspaces of F_2^n, exactly."""
    if r < 0 or r > n:
        return 0
    num = den = 1
    for i in range(r):
        num *= (1 << (n - i)) - 1
        den *= (1 << (i + 1)) - 1
    return num // den


def rank_drop_exact(N, d):
    """P(T(L') != F_2^2) for L' uniform in Gr(F_2^N, d), T onto F_2^2.

    Inclusion-exclusion over the three lines of F_2^2: L' misses the full
    image iff L' lies in T^(-1)(line) (codim 1) for some line; two such
    preimages meet in ker T (codim 2), and all three meet in ker T as well.
    """
    tot = gauss_binom(N, d)
    one = gauss_binom(N - 1, d)
    two = gauss_binom(N - 2, d)
    bad = 3 * one - 3 * two + two
    return Fraction(bad, tot)


def part_a():
    print("(a) rank-drop lemma: max over N of P(rank <= 1) versus 3*2^(1-l)")
    worst = 0.0
    for l in range(2, 41):
        d = l - 1
        mx = max(rank_drop_exact(N, d) for N in range(max(d, 2), d + 60))
        bound = Fraction(3, 1 << (l - 1))
        assert mx <= bound, (l, mx, bound)
        worst = max(worst, float(mx / bound))
        if l in (2, 3, 4, 5, 8, 12, 20, 40):
            print(f"  l={l:2d}  max_N P={float(mx):.6e}  bound={float(bound):.6e}"
                  f"  ratio={float(mx / bound):.4f}")
    print(f"  all l in [2,40], N in [l-1, l+58]: P <= bound (worst ratio {worst:.4f})")


def rho_bound(l, k, pistar=0.0):
    beta = math.log(math.log(k)) / k
    gamma = 2.0 ** (l - 2 * k) * (math.exp(3 * beta * k) / 2 + 1)
    drop = 3 * 2.0 ** (1 - l)
    den = (1 - gamma) * ((1 - beta) * (1 - drop) - gamma - pistar)
    if den <= 0:
        return float("inf"), beta, gamma
    return (beta + drop) / den, beta, gamma


def part_b():
    print("(b) Theorem F bound lambda_2 <= 1 - sqrt(1 - rho) at beta = ln ln k / k")
    for l in (6, 8, 10, 12, 16, 20):
        for k in (10 ** 4, 10 ** 6, 10 ** 9):
            r, beta, gamma = rho_bound(l, k)
            lam = 1 - math.sqrt(1 - r) if r < 1 else float("nan")
            print(f"  l={l:2d} k={k:.0e} beta={beta:.2e} gamma={gamma:.1e}"
                  f"  rho={r:.3e}  lambda_2<={lam:.3e}  12*2^-l+2beta={12 * 2.0 ** -l + 2 * beta:.3e}")
    print("    (pi* = 0 here; pi* <= mu k/((1-nu)(1-gamma) m) -> 0 as n -> oo at fixed k)")
    print("(b') least l with 12*2^-l < X*eta'/2 (then gate (G) is vacuous once 2beta < X*eta'/2)")
    for X in (3, 10, 100):
        for eta in (1e-2, 1e-5, 1e-9):
            lstar = math.ceil(math.log2(24 / (X * eta)) + 1e-12)
            print(f"  X(delta)={X:3d} eta'={eta:.0e}: l >= {lstar}")
    # sanity of the simplified form: for l>=6, beta<=1/32, gamma+pi*<=1/32, rho <= 2(beta+6*2^-l)
    for l in range(6, 60):
        for beta in (0.0, 1 / 64, 1 / 32):
            g = 1 / 32
            drop = 3 * 2.0 ** (1 - l)
            rho = (beta + drop) / ((1 - g) * ((1 - beta) * (1 - drop) - g))
            assert rho <= 2 * (beta + 6 * 2.0 ** -l), (l, beta, rho)
    print("  simplified form rho <= 2(beta + 6*2^-l) checked for l in [6,59], beta <= 1/32, gamma+pi* <= 1/32")


def part_c():
    here = os.path.dirname(os.path.abspath(__file__))
    sys.path.insert(0, os.path.join(here, "..", "ugc-akkstv-regularize-2026-09-17"))
    import dkkms_folded_gap_large as G  # noqa: E402

    def frozen(U, K, EQ):
        # triples of U-equations e with rank of K -> F_2^e/<111> equal to 2
        # (K = L + H_U has the same projection mod <111> as L)
        out = set()
        for i in U:
            a, b, c = EQ[i]
            cls = set()
            for z in K:
                bits = ((z >> a) & 1, (z >> b) & 1, (z >> c) & 1)
                if bits in ((1, 0, 0), (0, 1, 1)):
                    cls.add(0)
                elif bits in ((0, 1, 0), (1, 0, 1)):
                    cls.add(1)
                elif bits in ((0, 0, 1), (1, 1, 0)):
                    cls.add(2)
            if len(cls) == 3:
                out.add(EQ[i])
        return frozenset(out)

    rng = random.Random(20260918)
    n, D, k, l = 24, 2, 2, 2
    EQ = G.regular_3lin(n, D, rng)
    for beta in (0.0, 0.1):
        tuples, HUs, Aun, Akey, B, Wun, Wkey = G.build(EQ, k, l, beta)
        amap, ex = G.canonical(HUs, Akey, l, Wkey)
        lam, ncls = G.gap(Wkey, len(Akey), len(B), amap)
        # class statistic F(c) = intersection of Frozen over members (a class function)
        Fc = {}
        inv_ok = inv_tot = 0
        members = defaultdict(list)
        for (U, K), i in Akey.items():
            members[amap[i]].append(frozen(U, K, EQ))
        for c, fs in members.items():
            inter = frozenset.intersection(*fs)
            Fc[c] = inter
            inv_tot += 1
            inv_ok += all(f == inter for f in fs)
        W = defaultdict(float)
        for (a, b), w in Wkey.items():
            W[(amap[a], b)] += w
        wb = defaultdict(float)
        wc = defaultdict(float)
        byb = defaultdict(list)
        for (c, b), w in W.items():
            wb[b] += w
            wc[c] += w
            byb[b].append((c, w))
        tot = sum(wb.values())
        EF = sum(wc[c] * len(Fc[c]) for c in wc) / tot
        p = defaultdict(float)
        for c in wc:
            for t in Fc[c]:
                p[t] += wc[c] / tot
        sump2 = sum(v * v for v in p.values())
        # E|F(c) cap F(c')| over the two-step walk c -> b -> c'
        Einter = 0.0
        for b, lst in byb.items():
            cnt = defaultdict(float)
            for c, w in lst:
                for t in Fc[c]:
                    cnt[t] += w
            Einter += sum(v * v for v in cnt.values()) / wb[b]
        Einter /= tot
        Elost = EF - Einter
        rho = Elost / (EF - sump2)
        ub = 1 - math.sqrt(max(0.0, 1 - rho))
        print(f"(c) n={n} k={k} l={l} beta={beta}: classes={ncls} exact-mass={ex:.3f}"
              f"  frozen-invariant classes={inv_ok}/{inv_tot}")
        print(f"    E|F|={EF:.4f}  E|lost|={Elost:.4f}  sum p^2={sump2:.4f}"
              f"  rho={rho:.4f}  lambda_2={lam:.5f}  <=  1-sqrt(1-rho)={ub:.5f}")
        assert lam <= ub + 1e-9


if __name__ == "__main__":
    part_a()
    part_b()
    if "--instance" in sys.argv:
        part_c()
    sys.exit(0)
