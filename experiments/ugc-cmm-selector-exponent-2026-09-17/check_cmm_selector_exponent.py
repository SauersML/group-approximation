#!/usr/bin/env python3
"""Checks for selector-bias-is-capped-by-the-cmm-alphabet-soundness-exponent.

1. Symbolic identities.
   e(eps) = eps/(2-eps) is the CMM Theorem 3.1 exponent.
   (a) e(1-c) = (1-c)/(1+c), and c_max(s) = (1-s)/(1+s) inverts it.
   (b) e((1+eta)/2) = (1+eta)/(3-eta) is the CMM Section 5 d-to-1 exponent
       (d-1+eta)/(d+1-eta) at d = 2 (the trivial-orientation route).
   (c) c_max(1/3) = 1/2: at the CMM-optimal 2-to-1 exponent no bias above 1/2 survives.
2. Monotonicity of g(eps,k) in eps on a grid (used to apply CMM at eps >= eps*).
3. Exhaustive toy check of the pull-back step: for random 2-to-1 games with
   k = 4 (right alphabet 2) and every orientation and every lift labelling,
   the pulled-back labelling of G has value >= the lift labelling's value,
   and val(G)/2 <= val(U_o) <= val(G).
4. Illustrative table (c_0 = 1): least l = log2 k with g(eps, 2^l) >= 2 delta
   at delta = 2^(-s l), showing the kill threshold s > e(eps) + o(1).
"""
import itertools
import math
import random

import sympy as sp

eps, c, s, eta = sp.symbols("eps c s eta", positive=True)
e = eps / (2 - eps)

# 1(a)
assert sp.simplify(e.subs(eps, 1 - c) - (1 - c) / (1 + c)) == 0
cmax = (1 - s) / (1 + s)
assert sp.simplify(((1 - cmax) / (1 + cmax)) - s) == 0
# 1(b)
d = 2
assert sp.simplify(e.subs(eps, (1 + eta) / 2) - (d - 1 + eta) / (d + 1 - eta)) == 0
# 1(c)
assert cmax.subs(s, sp.Rational(1, 3)) == sp.Rational(1, 2)
print("1. identities: e(1-c)=(1-c)/(1+c); c_max(s)=(1-s)/(1+s); "
      "e((1+eta)/2)=(1+eta)/(3-eta); c_max(1/3)=1/2  -- ok")


def g(ep, k, c0=1.0):
    lk = math.log(k)
    m = 1.0 if ep * lk <= 1 else 1.0 / math.sqrt(ep * lk)
    return c0 * m * (1 - ep) ** 2 * (k / math.sqrt(lk)) ** (-ep / (2 - ep))


# 2
for k in [2, 3, 4, 8, 16, 2 ** 10, 2 ** 40, 2 ** 200]:
    vals = [g(i / 1000, k) for i in range(0, 1000)]
    assert all(vals[i] >= vals[i + 1] - 1e-15 for i in range(len(vals) - 1)), k
print("2. g(eps,k) non-increasing in eps on grid, k in {2..2^200} -- ok")

# 3
rng = random.Random(20260920)
K, R = 4, 2  # left alphabet [4], right alphabet [2], projections exactly 2-to-1
checked = 0
for trial in range(40):
    P, Q = 2, 2
    edges = []
    for _ in range(3):
        p, q = rng.randrange(P), rng.randrange(Q)
        perm = list(range(K))
        rng.shuffle(perm)
        pi = {perm[0]: 0, perm[1]: 0, perm[2]: 1, perm[3]: 1}
        edges.append((p, q, pi))

    def valG(sig, tau):
        return sum(pi[sig[p]] == tau[q] for p, q, pi in edges) / len(edges)

    vG = max(valG(sg, t) for sg in itertools.product(range(K), repeat=P)
             for t in itertools.product(range(R), repeat=Q))
    # orientations: per edge, per fibre, which element gets bit 0
    fibres = [[[a for a in range(K) if pi[a] == b] for b in range(R)] for _, _, pi in edges]
    for choice in itertools.product([0, 1], repeat=len(edges) * R):
        o = []
        for i, (_, _, pi) in enumerate(edges):
            oe = {}
            for b in range(R):
                x, y = fibres[i][b]
                bit = choice[i * R + b]
                oe[x], oe[y] = bit, 1 - bit
            o.append(oe)
        best = 0.0
        for sg in itertools.product(range(K), repeat=P):
            for t in itertools.product(itertools.product(range(R), [0, 1]), repeat=Q):
                sat = sum((pi[sg[p]], o[i][sg[p]]) == t[q]
                          for i, (p, q, pi) in enumerate(edges)) / len(edges)
                pull = valG(sg, tuple(tt[0] for tt in t))
                assert pull >= sat - 1e-12
                best = max(best, sat)
                checked += 1
        assert vG / 2 - 1e-12 <= best <= vG + 1e-12
print(f"3. pull-back dominates lift value and sandwich holds on {checked} "
      "(game, orientation, labelling) triples -- ok")

# 4
print("4. least l with g(eps,2^l) >= 2*2^(-s l)  (c_0 = 1, illustrative)")
print("   bias c   e(1-c)    s=e+0.02   s=e+0.05   s=1/3")
for cc in [0.55, 0.6, 0.75, 0.9, 0.99]:
    ep = 1 - cc
    ee = ep / (2 - ep)
    row = []
    for ss in [ee + 0.02, ee + 0.05, 1 / 3]:
        if ss <= ee:
            row.append("   none")
            continue
        l = 2
        while l < 100000 and g(ep, 2.0 ** l) < 2 * 2.0 ** (-ss * l):
            l += 1
        row.append(f"{l:>9d}")
    print(f"   {cc:5.2f}   {ee:.4f}  " + "  ".join(row))
