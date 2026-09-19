#!/usr/bin/env python3
"""Instance-free labelling of the folded DKKMS 2-to-1 game (TR16-198 Sec. 4.2).

Node: dkkms-2to1-value-is-at-least-seed-concentration.

The labelling (Theorem LV of the node) uses no global assignment:
  * A at class C = (U, Lbar): pick the hyperplane P* of Lbar with the largest
    score s(P) = #{blocks i : dim pi_i(P) <= 1} (ties: least sorted vector
    tuple, a rule intrinsic to the subspace).  Block by block:
      pi_i(P*) = <ebar_v>  ->  x_i = satisfying assignment of e_i with x(v)=0
                               (least other variable carries b_i);
      otherwise            ->  x_i = c_{e_i} (least variable carries b_i).
  * B at (V, L'): kept block i -> the same rule applied to the true block
    image Q_i of L' (B knows e_i); smoothed block with variable v -> y(v)=0.

Part A (exact, per sample): x satisfies every equation of U, and whenever
  P* equals the true seed Q = (L' + H_U)/H_U the constraint x|L' = y|L'
  holds (checked on a basis of L').  Any failure is reported and exits 1.
Part B (Monte Carlo): identification rate Pr[P* = Q] at fixed beta = 0.5 and
  0.25 against k, and at the DKKMS rate beta = log log k / k.
Part C: the explicit Hoeffding bound of Lemma ID versus the empirical
  misidentification rate (the bound must dominate).
The RHS bits b_i are uniform: the labelling never reads the instance beyond
the equations of the tuple, so every instance (satisfiable or not) is covered.
Seed 20260919.  Exit 0 iff Part A has 0 failures, Part B shows
Pr[P* = Q] >= 0.99 at beta = 0.5, l = 3, k = 400, and Part C holds with at
least one non-vacuous row (bound < 0.05, at k = 3000).
"""
import math
import random
import sys

SEED = 20260919


def qblock(b):
    # F_2^3/<111> -> F_2^2 ; ebar_0 = 1, ebar_1 = 2, ebar_2 = 3
    b0, b1, b2 = b & 1, (b >> 1) & 1, (b >> 2) & 1
    return (b0 ^ b2) | ((b1 ^ b2) << 1)


EBAR_TO_VAR = {1: 0, 2: 1, 3: 2}


def qmap(vec, k):
    out = 0
    for i in range(k):
        out |= qblock((vec >> (3 * i)) & 7) << (2 * i)
    return out


def rank(vecs):
    basis = []
    for v in vecs:
        for bv in basis:
            v = min(v, v ^ bv)
        if v:
            basis.append(v)
    return len(basis)


def span(vecs):
    s = {0}
    for v in vecs:
        s |= {u ^ v for u in s}
    return s


def block_image(subspace_vecs, i):
    return {(p >> (2 * i)) & 3 for p in subspace_vecs}


def block_rule(img, b):
    """Local assignment (3 bits) of an equation with RHS b given block image."""
    if len(img) == 2:  # one-dimensional: <ebar_v>
        r = max(img)
        v = EBAR_TO_VAR[r]
        others = [u for u in range(3) if u != v]
        return b << others[0]
    return b  # least variable carries b


def sample_edge(k, l, beta, rng):
    while True:
        kind = []
        for _ in range(k):
            kind.append(-1 if rng.random() >= beta else rng.randrange(3))
        cols = []
        for _ in range(l - 1):
            w = 0
            for i, t in enumerate(kind):
                if t < 0:
                    w |= rng.randrange(8) << (3 * i)
                elif rng.randrange(2):
                    w |= 1 << (3 * i + t)
            cols.append(w)
        cols.append(rng.getrandbits(3 * k))
        tb = [qmap(c, k) for c in cols]
        if rank(tb) == l:  # T-bar injective: (U,L) in A, L' of dim l-1
            return kind, cols, tb


def hyperplanes(tb, l):
    out = []
    for psi in range(1, 1 << l):
        ker = [c for c in range(1, 1 << l) if bin(c & psi).count("1") % 2 == 0]
        vecs = set()
        for c in ker:
            v = 0
            for j in range(l):
                if (c >> j) & 1:
                    v ^= tb[j]
            vecs.add(v)
        vecs.add(0)
        out.append((psi, frozenset(vecs)))
    return out


def score(P, k):
    return sum(1 for i in range(k) if len(block_image(P, i)) <= 2)


def run_sample(k, l, beta, rng):
    kind, cols, tb = sample_edge(k, l, beta, rng)
    rhs = [rng.randrange(2) for _ in range(k)]
    Q = frozenset(span(tb[: l - 1]))
    hp = hyperplanes(tb, l)
    best = max(hp, key=lambda t: (score(t[1], k), [-x for x in sorted(t[1])]))
    Pstar = best[1]
    # A's assignment
    x = 0
    for i in range(k):
        x |= block_rule(block_image(Pstar, i), rhs[i]) << (3 * i)
    sat = all(bin((x >> (3 * i)) & 7).count("1") % 2 == rhs[i] for i in range(k))
    # B's assignment on V's variables
    y = 0
    for i, t in enumerate(kind):
        if t < 0:
            y |= block_rule(block_image(Q, i), rhs[i]) << (3 * i)
        # smoothed: y(v) = 0, nothing to set
    agree = all(bin(x & w).count("1") % 2 == bin(y & w).count("1") % 2
                for w in cols[: l - 1])
    ident = Pstar == Q
    return sat, ident, agree


def hoeffding_bound(k, l, beta):
    d = 0.5 - 2.0 ** (1 - l)
    return (2 ** l - 2) * math.exp(-beta ** 2 * d ** 2 * k / 8) + math.exp(-beta * k / 8)


def main():
    rng = random.Random(SEED)
    fails = 0
    ok = True
    print("Part A+B: fixed beta, identification and exact agreement")
    print(" l  beta    k   N   Pr[P*=Q]  Pr[agree]  sat_fail  agree_fail_when_ident")
    rows = [(3, 0.5, 50), (3, 0.5, 100), (3, 0.5, 200), (3, 0.5, 400),
            (4, 0.5, 200), (3, 0.25, 100), (3, 0.25, 400), (5, 0.25, 400),
            (3, 0.5, 3000)]
    table = {}
    for l, beta, k in rows:
        N = 300 if k <= 400 else 40
        idc = agc = sf = af = 0
        for _ in range(N):
            sat, ident, agree = run_sample(k, l, beta, rng)
            sf += (not sat)
            idc += ident
            agc += agree
            af += (ident and not agree)
        fails += sf + af
        table[(l, beta, k)] = (idc / N, N)
        print(f" {l}  {beta:.2f} {k:4d} {N}   {idc/N:.3f}     {agc/N:.3f}      {sf}         {af}")
    print("Part B': DKKMS rate beta = log log k / k (flat seed law expected)")
    for l, k in [(3, 100), (3, 400)]:
        beta = math.log(math.log(k)) / k
        N = 300
        idc = agc = 0
        for _ in range(N):
            sat, ident, agree = run_sample(k, l, beta, rng)
            fails += (not sat) + (ident and not agree)
            idc += ident
            agc += agree
        print(f" l={l} k={k} beta={beta:.4f}: Pr[P*=Q]={idc/N:.3f} Pr[agree]={agc/N:.3f}"
              f"  (1/(2^l-1) = {1/(2**l-1):.3f})")
    print("Part C: Hoeffding bound of Lemma ID vs empirical misidentification")
    nonvacuous = False
    for (l, beta, k), (r, N) in table.items():
        hb = hoeffding_bound(k, l, beta) / (1 - 2.0 ** (l - k))
        nonvacuous |= hb < 0.05
        good = (1 - r) <= hb + 3 * math.sqrt(max(r * (1 - r), 1e-9) / N) + 0.02 or hb >= 1
        print(f" l={l} beta={beta} k={k}: empirical {1-r:.3f}  bound {min(hb,1):.3f}  {'ok' if good else 'VIOLATED'}")
        ok &= good
    ok &= fails == 0
    ok &= table[(3, 0.5, 400)][0] >= 0.99
    ok &= nonvacuous
    print("Part A failures:", fails)
    print("ALL PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
