#!/usr/bin/env python3
"""The DKKMS seed law at the paper's own smoothing rate beta = log log k / k.

Claim node: `dkkms-seed-law-is-uniform-in-regime-and-far-in-window`.

Fix a k-tuple U.  The DKKMS edge law draws a smoothing V (each block kept with
probability 1 - beta, otherwise replaced by one uniform variable), a seed
R uniform in Gr(X_V, l-1), and an A-space L > R uniform among the valid
extensions.  Write P0 for the law of R and Q for the uniform law on
Gr(X_U, l-1).

Closed form (Section 1 below, checked against the exact rational DP of
experiments/grassmann-99-rigidity-2026-09-18/seed_spread_dkkms.py).  Put
a = 4^(l-1).  For an (l-1)-space R let

    n0(R) = #blocks where the projection of R is 0,
    n1(R) = #blocks where the projection of R is a coordinate axis <e_v>.

Then, up to a factor exp(+- 4 l 2^(l-k)) that is uniform in R,

    P0(R) / Q(R)  =  (1-beta)^k * (1 + beta a/(1-beta))^n0 * (1 + beta a/(3(1-beta)))^n1.

Because every block is independent, n0 and n1 have multinomial laws, and this
lets us sample at any k (k = 2^60 is fine), which the rational DP cannot do.

What is printed:

  1. pointwise check of the closed form against the exact DP;
  2. TV(P0, Q) by Monte Carlo, against the covering bound
     d = beta sqrt(k) 2^(l+3), the Gaussian heuristic, and the analytic lower
     bound LB = 1 - (1-beta)^k - 3 k 4^(1-l);
  3. the conditional seed law w(.|L) at an A-vertex: E_L max_R w(R|L),
     E_L TV(w(.|L), uniform on the 2^l - 1 hyperplanes), and how often the
     dominant hyperplane is the generating seed, along beta = log log k / k.
  4. the admissible-but-uncertified window (q = 1) for large l, analytically.

Run: python3 experiments/dkkms-covering-window-2026-09-17/seed_law_at_dkkms_beta.py
"""

from __future__ import annotations

import math
import os
import random
import sys
from fractions import Fraction

import numpy as np

SEED = 20260917

HERE = os.path.dirname(os.path.abspath(__file__))
OLD = os.path.join(HERE, "..", "grassmann-99-rigidity-2026-09-18")


def beta_of(k: float) -> float:
    """DKKMS: beta = log log k / k (natural logarithms)."""
    return math.log(math.log(k)) / k


# ---------------------------------------------------------------------------
# Block patterns.  A block pattern of an l-space L = span(r_1..r_{l-1}, x) is
# the tuple of the projections (b_1, ..., b_l) in F_2^3 of the basis to that
# block; b_l is the projection of the direction x.  Hyperplanes of L are
# R_c = { sum a_i basis_i : a . c = 0 } for c in F_2^l \ 0; the generating seed
# span(r_1..r_{l-1}) is c = 1 << (l-1).
# ---------------------------------------------------------------------------

AXES = (1, 2, 4)


def block_type(image: set) -> int:
    """0: projection is zero; 1: projection is a coordinate axis; 2: other."""
    nz = image - {0}
    if not nz:
        return 0
    if len(nz) == 1 and next(iter(nz)) in AXES:
        return 1
    return 2


def hyperplane_image(pattern, c: int, l: int) -> set:
    img = set()
    for a in range(1 << l):
        if bin(a & c).count("1") % 2:
            continue
        v = 0
        for i in range(l):
            if (a >> i) & 1:
                v ^= pattern[i]
        img.add(v)
    return img


def pattern_index(pattern) -> int:
    idx = 0
    for i, b in enumerate(pattern):
        idx |= b << (3 * i)
    return idx


def pattern_tables(l: int):
    """T0[p, c], T1[p, c] indicators, and the smoothed-block pattern list."""
    P = 8 ** l
    H = (1 << l) - 1
    T0 = np.zeros((P, H), dtype=np.int64)
    T1 = np.zeros((P, H), dtype=np.int64)
    for idx in range(P):
        pat = [(idx >> (3 * i)) & 7 for i in range(l)]
        for c in range(1, 1 << l):
            t = block_type(hyperplane_image(pat, c, l))
            if t == 0:
                T0[idx, c - 1] = 1
            elif t == 1:
                T1[idx, c - 1] = 1
    smoothed = []
    for v in AXES:
        for rmask in range(1 << (l - 1)):
            for xb in range(8):
                pat = [v if (rmask >> i) & 1 else 0 for i in range(l - 1)] + [xb]
                smoothed.append(pattern_index(pat))
    return T0, T1, np.array(smoothed, dtype=np.int64)


def log_lr(n0, n1, k: float, beta: float, l: int):
    """log of P0(R)/Q(R) by the closed form (natural log)."""
    a = 4.0 ** (l - 1)
    A0 = math.log1p(beta * a / (1.0 - beta))
    A1 = math.log1p(beta * a / (3.0 * (1.0 - beta)))
    return k * math.log1p(-beta) + n0 * A0 + n1 * A1


def sample_A_vertex_fast(old, B, beta: float, l: int, rng: random.Random):
    """Explicit draw of (V, L', L) from the DKKMS edge law.

    Same law as seed_spread_dkkms.sample_A_vertex, but X_V is a coordinate
    subspace, so a uniform vector of X_V is a uniform mask on the kept
    variables; this avoids enumerating X_V.
    """
    Hb = old.rref(B.H)
    while True:
        keptmask = 0
        for i in range(B.k):
            if rng.random() < beta:
                keptmask |= rng.choice(B.vars[i])
            else:
                keptmask |= B.masks[i]
        vecs = [rng.getrandbits(B.n) & keptmask for _ in range(l - 1)]
        Lp = old.rref(vecs)
        if len(Lp) != l - 1:
            continue
        x = rng.getrandbits(B.n)
        L = old.rref(list(Lp) + [x])
        if len(L) != l:
            continue
        if len(old.rref(list(L) + list(Hb))) != l + B.k:
            continue  # L cap H_U != 0
        return L, Lp


# ---------------------------------------------------------------------------
# Section 1: the closed form against the exact rational DP.
# ---------------------------------------------------------------------------

def section1(rng: random.Random) -> float:
    sys.path.insert(0, OLD)
    import seed_spread_dkkms as old  # noqa: E402  (read-only reuse)

    print("1. closed form versus the exact rational DP of seed_spread_dkkms.py")
    print(f"   {'k':>3} {'l':>2} {'beta':>8} {'max |w_exact - w_closed|':>26}"
          f" {'max rel err of P0/Q':>21} {'4 l 2^(l-k)':>12}")
    worst = 0.0
    for k, l in ((6, 2), (8, 2), (10, 2), (6, 3), (8, 3), (10, 3), (9, 4)):
        beta_f = Fraction(beta_of(k)).limit_denominator(10 ** 6)
        beta = float(beta_f)
        B = old.Blocks(k)
        err_w = err_lr = 0.0
        for _ in range(12):
            L, _Lp = sample_A_vertex_fast(old, B, beta, l, rng)
            hs = old.hyperplanes(L)
            exact = [old.unnormalised_seed_weight(B, R, beta_f, l) for R in hs]
            g = old.gauss_count(3 * k, l - 1)
            closed = []
            for R in hs:
                n0 = n1 = 0
                for i in range(k):
                    adm = len(B.block_profile(R, i))
                    n0 += adm == 3
                    n1 += adm == 1
                closed.append(math.exp(log_lr(n0, n1, k, beta, l)))
            for e, c in zip(exact, closed):
                err_lr = max(err_lr, abs(float(e * g) / c - 1.0))
            te, tc = sum(exact), sum(closed)
            for e, c in zip(exact, closed):
                err_w = max(err_w, abs(float(e / te) - c / tc))
        bound = 4 * l * 2.0 ** (l - k)
        worst = max(worst, err_lr / bound)
        print(f"   {k:>3} {l:>2} {beta:>8.5f} {err_w:>26.3e} {err_lr:>21.3e} {bound:>12.3e}")
    assert worst <= 1.0, worst
    print("   OK: the relative error of the closed form is within 4 l 2^(l-k).")
    print()
    return worst


# ---------------------------------------------------------------------------
# Section 2: TV(P0, Q) along beta = log log k / k.
# Under Q an (l-1)-space is spanned by l-1 i.i.d. uniform vectors up to TV
# 2^(l-1-3k); their block projections are i.i.d. uniform in (F_2^3)^(l-1), so
# (n0, n1, n2) is multinomial(k; p0, p1, p2) with p0 = 8^(1-l) and
# p1 = 3 (2^(l-1) - 1) 8^(1-l).  TV = E_Q (1 - P0/Q)_+.
# ---------------------------------------------------------------------------

def tv_mc(k: int, l: int, nrng: np.random.Generator, n: int = 200000):
    beta = beta_of(k)
    p0 = 8.0 ** (1 - l)
    p1 = 3.0 * (2.0 ** (l - 1) - 1.0) * 8.0 ** (1 - l)
    cnt = nrng.multinomial(k, [p0, p1, 1.0 - p0 - p1], size=n)
    a = 4.0 ** (l - 1)
    A0 = math.log1p(beta * a / (1.0 - beta))
    A1 = math.log1p(beta * a / (3.0 * (1.0 - beta)))
    llr = k * math.log1p(-beta) + cnt[:, 0] * A0 + cnt[:, 1] * A1
    lr = np.exp(np.minimum(llr, 50.0))
    tv = float(np.mean(np.maximum(0.0, 1.0 - lr)))
    se = float(np.std(np.maximum(0.0, 1.0 - lr)) / math.sqrt(n))
    return tv, se, beta


def covering_d(k: float, l: int) -> float:
    return beta_of(k) * math.sqrt(k) * 2.0 ** (l + 3)


def lower_bound(k: float, l: int) -> float:
    beta = beta_of(k)
    return max(0.0, 1.0 - math.exp(k * math.log1p(-beta)) - 3.0 * k * 4.0 ** (1 - l))


def gauss_heuristic(k: float, l: int) -> float:
    s = beta_of(k) * math.sqrt(k / 3.0) * 2.0 ** (l - 1)
    return math.erf(s / (2.0 * math.sqrt(2.0)))


def section2(nrng: np.random.Generator):
    print("2. TV(P0, Q) between the DKKMS seed law and the uniform (l-1)-space")
    print(f"   {'l':>2} {'log2 k':>6} {'TV (MC)':>9} {'+-':>7} {'covering d':>11}"
          f" {'Gauss':>7} {'LB':>7}")
    out = {}
    for l in (2, 3, 4, 5):
        for e in (6, 10, 14, 18, 22, 26, 30, 34, 38, 44, 50, 56):
            k = 2 ** e
            tv, se, _ = tv_mc(k, l, nrng)
            d = covering_d(k, l)
            lb = lower_bound(k, l)
            out[(l, e)] = tv
            # the rigorous facts: LB <= TV always; TV <= d whenever d is a bound
            assert tv >= lb - 4 * se - 1e-3, (l, e, tv, lb)
            if 2.0 ** (l - 1) * beta_of(k) <= 1 / 8:
                assert tv <= d + 4 * se + 1e-3, (l, e, tv, d)
            print(f"   {l:>2} {e:>6} {tv:>9.5f} {se:>7.1e} {min(d, 99):>11.4g}"
                  f" {gauss_heuristic(k, l):>7.4f} {lb:>7.4f}")
    print("   OK: LB <= TV <= covering d wherever the covering lemma applies.")
    print()
    return out


# ---------------------------------------------------------------------------
# Section 3: the conditional seed law at an A-vertex, w(R | L), along
# beta = log log k / k.  An A-vertex is drawn from the edge law block by block:
# m ~ Bin(k, beta) smoothed blocks, kept blocks carry uniform patterns in
# (F_2^3)^l, smoothed blocks carry r_i in <e_v> and a uniform x-projection.
# (We drop the conditionings "r_1..r_{l-1} independent" and "L cap H_U = 0",
# which cost TV at most 2^(l-k) + 2^(l-1-2k).)
# ---------------------------------------------------------------------------

def cond_stats(k: int, l: int, tables, nrng: np.random.Generator, n: int):
    T0, T1, smoothed = tables
    P = 8 ** l
    beta = beta_of(k)
    a = 4.0 ** (l - 1)
    A0 = math.log1p(beta * a / (1.0 - beta))
    A1 = math.log1p(beta * a / (3.0 * (1.0 - beta)))
    gen = (1 << (l - 1)) - 1
    H = (1 << l) - 1
    unif_p = np.full(P, 1.0 / P)
    sm_p = np.full(len(smoothed), 1.0 / len(smoothed))
    maxw = tvs = dom = 0.0
    for _ in range(n):
        m = int(nrng.binomial(k, beta))
        cnt = nrng.multinomial(k - m, unif_p).astype(np.int64)
        if m:
            sc = nrng.multinomial(m, sm_p)
            cnt += np.bincount(smoothed, weights=sc, minlength=P).astype(np.int64)
        n0 = cnt @ T0
        n1 = cnt @ T1
        lw = n0 * A0 + n1 * A1
        lw = lw - lw.max()
        w = np.exp(lw)
        w /= w.sum()
        maxw += float(w.max())
        tvs += 0.5 * float(np.abs(w - 1.0 / H).sum())
        dom += float(int(np.argmax(w)) == gen)
    return maxw / n, tvs / n, dom / n


def section3(nrng: np.random.Generator, tv_joint: dict):
    print("3. conditional seed law w(.|L) at beta = log log k / k")
    print(f"   {'l':>2} {'log2 k':>6} {'1/(2^l-1)':>9} {'E max w':>8} {'E TV(w,u)':>10}"
          f" {'dom=seed':>9} {'2 TV(P0,Q)':>11}")
    rows = []
    for l, reps in ((2, 3000), (3, 1500), (4, 400)):
        tables = pattern_tables(l)
        for e in (6, 10, 14, 18, 22, 26, 30, 34, 38, 44, 50, 56):
            k = 2 ** e
            mw, tv, dom = cond_stats(k, l, tables, nrng, reps)
            joint = tv_joint.get((l, e))
            # Lemma (conditioning): E_L TV(w(.|L), u) <= 2 TV(P, nu0); allow MC slack.
            if joint is not None:
                assert tv <= 2 * joint + 0.03 + 2 * (2.0 ** (l - k)), (l, e, tv, joint)
            rows.append((l, e, mw, tv, dom))
            js = f"{2 * joint:>11.4f}" if joint is not None else f"{'-':>11}"
            print(f"   {l:>2} {e:>6} {1 / ((1 << l) - 1):>9.4f} {mw:>8.4f} {tv:>10.4f}"
                  f" {dom:>9.3f} {js}")
    print("   OK: E_L TV(w(.|L), uniform) <= 2 TV(P0, Q) at every point.")
    print()
    return rows


def validate_sampler(rng: random.Random, nrng: np.random.Generator):
    """The block sampler of Section 3 against the explicit sampler plus exact DP."""
    sys.path.insert(0, OLD)
    import seed_spread_dkkms as old  # noqa: E402

    print("3a. block sampler versus explicit sampling + exact DP (l = 3)")
    tables = pattern_tables(3)
    for k in (10, 12):
        beta_f = Fraction(beta_of(k)).limit_denominator(10 ** 6)
        B = old.Blocks(k)
        tops = []
        doms = 0
        for _ in range(150):
            L, Lp = sample_A_vertex_fast(old, B, float(beta_f), 3, rng)
            hs = old.hyperplanes(L)
            ws = [old.unnormalised_seed_weight(B, R, beta_f, 3) for R in hs]
            best = max(ws)
            tops.append(float(best / sum(ws)))
            doms += hs[ws.index(best)] == Lp
        mean_old, dom_old = sum(tops) / len(tops), doms / 150
        mw, _, dom = cond_stats(k, 3, tables, nrng, 3000)
        print(f"   k={k:>2}: explicit E max w = {mean_old:.4f} (dom=seed {dom_old:.2f}),"
              f" block sampler {mw:.4f} (dom=seed {dom:.2f})")
        assert abs(mean_old - mw) < 0.06, (k, mean_old, mw)
    print("   OK: agreement within Monte Carlo error.")
    print()


# ---------------------------------------------------------------------------
# Section 4: the admissible-but-uncertified window at q = 1.
#   k_A(l): least k with eps_k = exp(-k/e^l) <= p0^2/4, p0 = 2^(-l)/192
#           (Corollary A admissibility, the target's quantifier);
#   k_0(l): least k with SD*(l,k) <= 10^(-5) (regime (R), Corollary N);
#   k_T(l): 4^(l-1)/12, below which 3 k 4^(1-l) <= 1/4.
# On [k_A, k_T] the lower bound gives TV >= 3/4 - 1/ln k.
# ---------------------------------------------------------------------------

def sd_star(k: float, l: int) -> float:
    return covering_d(k, l) + 3.0 * 2.0 ** (l - k)


def least_k(pred, lo: float = 16.0) -> float:
    hi = lo
    while not pred(hi):
        hi *= 2.0
    lo = max(16.0, hi / 2.0)
    for _ in range(200):
        mid = math.sqrt(lo * hi)
        if pred(mid):
            hi = mid
        else:
            lo = mid
    return hi


def section4(nrng: np.random.Generator):
    print("4. the q = 1 window between Corollary A admissibility and regime (R)")
    print(f"   {'l':>3} {'log2 k_A':>9} {'log2 k_T':>9} {'log2 k_0':>9}"
          f" {'LB(k_A)':>8} {'TV(k_A) MC':>11} {'d(k_A)':>10} {'LB(k_T)':>8}")
    for l in (10, 15, 18, 20, 22, 25, 30, 35):
        kA = math.exp(l) * (2 * l * math.log(2) + math.log(4 * 192 ** 2))
        kT = 4.0 ** (l - 1) / 12.0
        k0 = least_k(lambda k: sd_star(k, l) <= 1e-5)
        lbA = lower_bound(kA, l)
        tvA, _, _ = tv_mc(int(kA), l, nrng, n=50000)
        lbT = lower_bound(kT, l) if kT >= kA else float("nan")
        assert tvA >= lbA - 0.01
        if kT >= kA:
            assert lbT >= 0.75 - 1.0 / math.log(kT) - 1e-9
        print(f"   {l:>3} {math.log2(kA):>9.2f} {math.log2(kT):>9.2f} {math.log2(k0):>9.2f}"
              f" {lbA:>8.4f} {tvA:>11.5f} {covering_d(kA, l):>10.3g} {lbT:>8.4f}")
    print("   Window [k_A, k_T] is non-empty from l = 20 on (k_T >= k_A), and there")
    print("   every coupling to the uniform flag test is off by TV >= 3/4 - 1/ln k.")
    print()


def main() -> int:
    rng = random.Random(SEED)
    nrng = np.random.default_rng(SEED)
    section1(rng)
    validate_sampler(rng, nrng)
    tvj = section2(nrng)
    section3(nrng, tvj)
    section4(nrng)
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
