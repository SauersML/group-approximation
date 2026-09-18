#!/usr/bin/env python3
"""Exact replay of lifts-over-multiscale-expanders-expand-unless-ug-value-large.

Setting: a d-regular multigraph H on V (edge measure uniform on directed
edges), permutations pi_(u,v) of [q] with pi_(v,u) = pi_(u,v)^-1, and the
label-extended graph L on V x [q]. For S <= V x [q] with |S| = |V| (measure
1/q): loads l_v = |S_v| (E l = 1), a_uv = |{i in S_u : pi_uv(i) in S_v}|,
nu = E_(u,v)[a_uv] = 1 - Phi_L(S), R = E[a_uv / (l_u l_v)] (value of the
random labeling from S; a_uv = 0 when a load is 0), B_T = {l > T},
W_t = {l >= t}, e(A) = Pr_(u,v)[u in A, v in A].

Checks, in exact rational arithmetic:
  (a) the master inequality, for several real T:
        nu <= T^2 R + 2 int_0^T Pr[u in B_T, v in W_t] dt + 2 int_T^q e(W_t) dt
  (b) the consequence nu <= T^2 R + 2/(tau T) + 2 int_(1/tau)^q e(W_t) dt
      for tau in {1/2, 1/3, 1/q}
  (c) R <= val(U) (exhaustive over labelings)
  (d) necessity: min_S Phi_L(S) <= 1 - val(U) and
      min_S Phi_L(S) <= min_(|W| = |V|/q) Phi_H(W)   (cylinders W x [q])
Tiny instances are searched exhaustively over all S of measure 1/q; larger ones
use random S. Exit code 0 iff every check passes.
Usage: python3 check_lift_rounding.py [seed]
"""
import itertools
import random
import sys
from fractions import Fraction as F


def random_instance(rng, n, d, q):
    """d-regular multigraph as union of d/2 random 2-factors from random
    permutations of V (each sigma gives directed edges v->sigma(v) and back)."""
    edges = []  # directed edges (u, v, perm) with perm a tuple on [q]
    for _ in range(d // 2):
        sigma = list(range(n))
        rng.shuffle(sigma)
        for u in range(n):
            v = sigma[u]
            p = list(range(q))
            rng.shuffle(p)
            inv = [0] * q
            for i, j in enumerate(p):
                inv[j] = i
            edges.append((u, v, tuple(p)))
            edges.append((v, u, tuple(inv)))
    return edges


def stats(n, q, edges, S):
    load = [0] * n
    Sv = [set() for _ in range(n)]
    for (v, i) in S:
        load[v] += 1
        Sv[v].add(i)
    m = len(edges)
    nu = F(0)
    R = F(0)
    for (u, v, p) in edges:
        a = sum(1 for i in Sv[u] if p[i] in Sv[v])
        nu += a
        if a:
            R += F(a, load[u] * load[v])
    return load, nu / m, R / m


def pair_prob(edges, A, B):
    return F(sum(1 for (u, v, _) in edges if u in A and v in B), len(edges))


def integral_steps(load, q, lo, hi, fn):
    """int_lo^hi fn(W_t) dt where W_t = {l >= t}; W_t is constant on (j-1, j]."""
    total = F(0)
    for j in range(1, q + 1):
        a, b = max(F(j - 1), lo), min(F(j), hi)
        if b > a:
            W = {v for v, l in enumerate(load) if l >= j}
            total += (b - a) * fn(W)
    return total


def master_rhs(edges, load, q, R, T):
    BT = {v for v, l in enumerate(load) if l > T}
    cross = integral_steps(load, q, F(0), T, lambda W: pair_prob(edges, BT, W))
    heavy = integral_steps(load, q, T, F(q), lambda W: pair_prob(edges, W, W))
    return T * T * R + 2 * cross + 2 * heavy


def consequence_rhs(edges, load, q, R, T, tau):
    tail = integral_steps(load, q, 1 / tau, F(q), lambda W: pair_prob(edges, W, W))
    return T * T * R + 2 / (tau * T) + 2 * tail


def value(n, q, edges):
    best = F(0)
    for lab in itertools.product(range(q), repeat=n):
        sat = sum(1 for (u, v, p) in edges if p[lab[u]] == lab[v])
        best = max(best, F(sat, len(edges)))
    return best


def check_S(edges, n, q, S, Ts, taus, fails):
    load, nu, R = stats(n, q, edges, S)
    for T in Ts:
        if nu > master_rhs(edges, load, q, R, T):
            fails.append(("master", S, T))
        for tau in taus:
            if T >= 1 / tau and nu > consequence_rhs(edges, load, q, R, T, tau):
                fails.append(("consequence", S, T, tau))
    return nu, R


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    fails = []
    checked = 0
    Ts = [F(1), F(3, 2), F(2), F(5, 2), F(3)]
    # exhaustive tiny instances
    for trial in range(4):
        n, d, q = 6, 4, 3
        edges = random_instance(rng, n, d, q)
        taus = [F(1, 2), F(1, 3)]
        pts = [(v, i) for v in range(n) for i in range(q)]
        val = value(n, q, edges)
        best_nu = F(0)
        best_R = F(0)
        for S in itertools.combinations(pts, n):
            nu, R = check_S(edges, n, q, S, Ts, taus, fails)
            checked += 1
            best_nu = max(best_nu, nu)
            best_R = max(best_R, R)
            if R > val:
                fails.append(("R>val", S))
        if best_nu < val:
            fails.append(("labeling set", trial))
        cyl = F(0)
        for W in itertools.combinations(range(n), n // q):
            cyl = max(cyl, pair_prob(edges, set(W), set(W)) * q)
        if best_nu < cyl:
            fails.append(("cylinder", trial))
        print(f"tiny trial {trial}: val={val} max nonexp(1/q)={best_nu} "
              f"best cylinder nonexp={cyl} max R={best_R}")
    # random S on larger instances
    for trial in range(30):
        n, d, q = rng.choice([(24, 4, 4), (30, 6, 5), (40, 4, 8)])
        edges = random_instance(rng, n, d, q)
        taus = [F(1, 2), F(1, 3), F(1, q)]
        pts = [(v, i) for v in range(n) for i in range(q)]
        for _ in range(40):
            if rng.random() < 0.5:
                S = rng.sample(pts, n)
            else:  # concentrated loads: heavy vertices
                heavy = rng.sample(range(n), max(1, n // q))
                S = [(v, i) for v in heavy for i in range(q)]
                rest = [pt for pt in pts if pt[0] not in heavy]
                S += rng.sample(rest, n - len(S))
            check_S(edges, n, q, S, Ts + [F(q)], taus, fails)
            checked += 1
    print(f"checked {checked} sets; failures: {len(fails)}")
    for f in fails[:10]:
        print("FAIL", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
