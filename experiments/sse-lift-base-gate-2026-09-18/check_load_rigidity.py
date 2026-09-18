#!/usr/bin/env python3
"""Exact replay of lift-yes-sets-are-labelings-unless-the-base-loses-a-cut.

Setting (same as experiments/ugc-sse-reframe-2026-09-17/check_lift_rounding.py):
a d-regular multigraph H on V with the uniform directed-edge law, permutations
pi_(u,v) of [q] with pi_(v,u) = pi_(u,v)^-1, and the label-extended graph L on
V x [q] joining (u,i) to (v, pi_uv(i)).  For S <= V x [q] with |S| = |V|
(measure 1/q):

    l_v = |S_v|,  E l = 1,  a_uv = |{i in S_u : pi_uv(i) in S_v}|,
    1 - Phi_L(S) = E_(u,v)[a_uv],
    P  = supp(S) = {v : l_v >= 1},   A_0 = V \\ P,
    A_1 = {v : l_v = 1},  zeta = 1 - mu(A_1),  beta = mu(A_0),
    x   = the canonical labeling: the unique element of S_v on A_1, else 0.

The claim's items, all checked in exact rational arithmetic with
eta = Phi_L(S) (so every set is tested at its own level, not at a fixed eta):

  (R0)  Pr[l_u != l_v] <= 2 eta                      (integrality of the loads)
  (R1)  E[l_u 1(v not in P)] <= eta   (load-weighted escape) and hence
        mu(P) Phi_H(P) = Pr[u in P, v not in P] <= eta     (P is nearly closed)
  (R2)  zeta <= 2 beta                               (mass balance E l = 1)
  (R3)  val(x) >= 1 - eta - 2 zeta  >= 1 - eta - 4 beta    (canonical labeling)
  (R4)  val(U) >= val(x)                             (exhaustive, tiny cases)
  (R5)  the Rayleigh identity behind the spectral gate: for 0 < mu(A) < 1 and
        f = 1_A - mu(A),
            E[(f_u - f_v)^2] / (2 E[f^2]) = Phi_H(A) / (1 - mu(A)),
        so lambda_2(H) <= Phi_H(A_0)/(1 - beta) whenever 0 < beta < 1.
  (R6)  the dichotomy actually used: for every eta_0 >= eta, either
        val(U) >= 1 - eta_0 - 4 sqrt(eta_0) or H has a set A_0 with
        mu(A_0) > sqrt(eta_0) and Phi_H(A_0) < sqrt(eta_0).
  (R7)  the consumer's branch bound: if beta > 0 and mu(P) > 0 then
        lambda_2(H) <= eta / (beta mu(P)), checked through (R5) as
        Rayleigh(1_A_0 - beta) <= eta / (beta mu(P)).

Instance families:
  A. random 4-regular instances, |V| = 6, q = 3, EVERY S of measure 1/q
     (exhaustive, with the exhaustive value of the game);
  B. planted-labeling instances (high value, so Phi_L(S_x) is small): the
     value-type YES witness;
  C. planted nearly-closed base sets: H is a disjoint union of blocks with a
     few crossing edges and S is a cylinder W x [q] over one block of measure
     1/q -- the cut-type YES witness, where beta = 1 - 1/q is large;
  D. random S on larger instances, including load-concentrated S.

Exit code 0 iff every check passes.
Usage: python3 check_load_rigidity.py [seed]
"""
import itertools
import math
import random
import sys
from fractions import Fraction as F


# ---------------------------------------------------------------- instances

def add_edge(edges, u, v, p):
    """Add the directed pair (u,v,p) and (v,u,p^-1)."""
    inv = [0] * len(p)
    for i, j in enumerate(p):
        inv[j] = i
    edges.append((u, v, tuple(p)))
    edges.append((v, u, tuple(inv)))


def random_instance(rng, n, d, q):
    """d-regular multigraph as a union of d/2 random permutation 2-factors."""
    edges = []
    for _ in range(d // 2):
        sigma = list(range(n))
        rng.shuffle(sigma)
        for u in range(n):
            p = list(range(q))
            rng.shuffle(p)
            add_edge(edges, u, sigma[u], p)
    return edges


def planted_instance(rng, n, d, q, noise):
    """Random instance whose permutations agree with a planted labeling lab on
    a (1-noise) fraction of the edges."""
    lab = [rng.randrange(q) for _ in range(n)]
    edges = []
    for _ in range(d // 2):
        sigma = list(range(n))
        rng.shuffle(sigma)
        for u in range(n):
            v = sigma[u]
            p = list(range(q))
            rng.shuffle(p)
            if rng.random() >= noise:
                # repair p so that p[lab[u]] == lab[v]
                j = p.index(lab[v])
                p[j], p[lab[u]] = p[lab[u]], p[j]
            add_edge(edges, u, v, p)
    return edges, lab


def block_instance(rng, n, d, q, nblocks, cross):
    """H = nblocks equal blocks, each a random d-regular graph, then `cross`
    degree-preserving rewirings across blocks (two intra-block edges in
    different blocks are cut and recrossed).  H stays d-regular, which is what
    the theorem assumes; permutations are random."""
    assert n % nblocks == 0
    size = n // nblocks
    pairs = []  # (u, v) undirected, one entry per edge
    for b in range(nblocks):
        base = [b * size + i for i in range(size)]
        for _ in range(d // 2):
            sigma = base[:]
            rng.shuffle(sigma)
            for k, u in enumerate(base):
                pairs.append((u, sigma[k]))
    for _ in range(cross):
        for _attempt in range(50):
            i, j = rng.randrange(len(pairs)), rng.randrange(len(pairs))
            (u1, v1), (u2, v2) = pairs[i], pairs[j]
            if u1 // size != u2 // size:
                pairs[i] = (u1, v2)
                pairs[j] = (u2, v1)
                break
    edges = []
    for (u, v) in pairs:
        p = list(range(q))
        rng.shuffle(p)
        add_edge(edges, u, v, p)
    return edges


# ---------------------------------------------------------------- quantities

def edge_prob(edges, pred):
    return F(sum(1 for e in edges if pred(e)), len(edges))


def stats(n, q, edges, S):
    load = [0] * n
    Sv = [set() for _ in range(n)]
    for (v, i) in S:
        load[v] += 1
        Sv[v].add(i)
    m = len(edges)
    stay = F(0)
    for (u, v, p) in edges:
        stay += sum(1 for i in Sv[u] if p[i] in Sv[v])
    return load, Sv, stay / m


def labeling_value(edges, lab):
    return edge_prob(edges, lambda e: e[2][lab[e[0]]] == lab[e[1]])


def exhaustive_value(n, q, edges):
    best = F(0)
    for lab in itertools.product(range(q), repeat=n):
        best = max(best, labeling_value(edges, lab))
    return best


def isqrt_upper(x, D=10 ** 7):
    """A rational r >= sqrt(x) with denominator D (x a Fraction >= 0)."""
    if x == 0:
        return F(0)
    n = x.numerator * D * D // x.denominator + 1
    return F(math.isqrt(n) + 1, D)


# ---------------------------------------------------------------- the checks

def check_S(n, q, edges, S, fails, tag, val=None):
    load, Sv, stay = stats(n, q, edges, S)
    eta = 1 - stay
    P = {v for v in range(n) if load[v] >= 1}
    A0 = {v for v in range(n) if load[v] == 0}
    A1 = {v for v in range(n) if load[v] == 1}
    beta = F(len(A0), n)
    zeta = 1 - F(len(A1), n)

    # (R0)
    if edge_prob(edges, lambda e: load[e[0]] != load[e[1]]) > 2 * eta:
        fails.append((tag, "R0"))
    # (R1)
    escape = F(sum(load[u] for (u, v, _) in edges if v not in P), len(edges))
    if escape > eta:
        fails.append((tag, "R1-load", escape, eta))
    cutP = edge_prob(edges, lambda e: (e[0] in P) and (e[1] not in P))
    if cutP > eta:
        fails.append((tag, "R1"))
    if cutP != edge_prob(edges, lambda e: (e[0] in A0) and (e[1] not in A0)):
        fails.append((tag, "R1-sym"))
    # (R2)
    if zeta > 2 * beta:
        fails.append((tag, "R2"))
    # (R3)
    lab = [min(Sv[v]) if load[v] == 1 else 0 for v in range(n)]
    vx = labeling_value(edges, lab)
    if vx < 1 - eta - 2 * zeta:
        fails.append((tag, "R3a", vx, 1 - eta - 2 * zeta))
    if vx < 1 - eta - 4 * beta:
        fails.append((tag, "R3b"))
    # (R4)
    if val is not None and val < vx:
        fails.append((tag, "R4"))
    # (R5)
    if 0 < beta < 1:
        num = edge_prob(edges, lambda e: (e[0] in A0) != (e[1] in A0))
        rayleigh = num / (2 * beta * (1 - beta))
        phiA0 = cutP / beta
        if rayleigh != phiA0 / (1 - beta):
            fails.append((tag, "R5"))
        # (R7)
        if rayleigh > eta / (beta * (1 - beta)):
            fails.append((tag, "R7"))
    # (R6): run the dichotomy at eta_0 = eta (the tightest level for this S)
    if eta > 0:
        r = isqrt_upper(eta)
        v_here = val if val is not None else vx
        branch1 = v_here >= 1 - eta - 4 * r
        branch2 = beta > r and cutP / beta < r
        if not (branch1 or branch2):
            fails.append((tag, "R6", eta, beta, v_here))
    return eta, beta, vx


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    fails = []
    checked = 0

    # A. exhaustive tiny instances
    for trial in range(3):
        n, d, q = 6, 4, 3
        edges = random_instance(rng, n, d, q)
        val = exhaustive_value(n, q, edges)
        pts = [(v, i) for v in range(n) for i in range(q)]
        best_stay = F(0)
        for S in itertools.combinations(pts, n):
            eta, beta, vx = check_S(n, q, edges, S, fails, f"A{trial}", val)
            best_stay = max(best_stay, 1 - eta)
            checked += 1
        print(f"A{trial}: |V|={n} q={q} val={val} max stay(1/q)={best_stay}")

    # B. planted labelings (value-type YES witnesses)
    for trial in range(8):
        n, d, q = rng.choice([(9, 4, 3), (12, 4, 4), (16, 6, 4)])
        noise = rng.choice([F(0), F(1, 20), F(1, 10), F(1, 5)])
        edges, lab = planted_instance(rng, n, d, q, float(noise))
        S = [(v, lab[v]) for v in range(n)]
        eta, beta, vx = check_S(n, q, edges, S, fails, f"B{trial}")
        checked += 1
        if beta != 0:
            fails.append((f"B{trial}", "labeling set has empty A_0"))
        print(f"B{trial}: n={n} q={q} Phi_L(S)={float(eta):.4f} "
              f"beta={float(beta):.4f} val(x)={float(vx):.4f}")

    # C. planted nearly-closed base sets (cut-type YES witnesses)
    for trial in range(8):
        q = rng.choice([3, 4, 5])
        nblocks, d = q, 4
        size = rng.choice([3, 4, 5])
        n = nblocks * size
        cross = rng.choice([0, 1, 2])
        edges = block_instance(rng, n, d, q, nblocks, cross)
        W = set(range(size))                      # one block, measure 1/q
        S = [(v, i) for v in W for i in range(q)]
        eta, beta, vx = check_S(n, q, edges, S, fails, f"C{trial}")
        checked += 1
        if beta != 1 - F(1, q):
            fails.append((f"C{trial}", "cylinder beta"))
        print(f"C{trial}: n={n} q={q} cross={cross} Phi_L(WxQ)={float(eta):.4f} "
              f"beta={float(beta):.4f} val(x)={float(vx):.4f}")

    # D. random and load-concentrated S on larger instances
    for trial in range(20):
        n, d, q = rng.choice([(24, 4, 4), (30, 6, 5), (40, 4, 8)])
        edges = random_instance(rng, n, d, q)
        pts = [(v, i) for v in range(n) for i in range(q)]
        for _ in range(25):
            if rng.random() < 0.5:
                S = rng.sample(pts, n)
            else:
                heavy = rng.sample(range(n), max(1, n // q))
                S = [(v, i) for v in heavy for i in range(q)]
                rest = [pt for pt in pts if pt[0] not in heavy]
                S += rng.sample(rest, n - len(S))
            check_S(n, q, edges, S, fails, f"D{trial}")
            checked += 1

    print(f"checked {checked} sets; failures: {len(fails)}")
    for f in fails[:10]:
        print("FAIL", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
