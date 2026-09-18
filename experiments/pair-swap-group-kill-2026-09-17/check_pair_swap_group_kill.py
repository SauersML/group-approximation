#!/usr/bin/env python3
"""Regression checks for pair-swap-groups-of-smooth-pairing-designs-contain-alt.

Bounded checks only; the all-n statements are proved in
research/pair-swap-group-kill-proof.md.

1. Switching lemma: on K_{2n}, 2n in {4,6,8}, the real edge weights w with
   sum_{e in M} w(e) constant over all perfect matchings M form a space of
   dimension 2n (the functions f(a)+f(b)); for 2n in {4,6} every 0/1 solution
   is empty, complete, a star or a co-star.
2. Exact 2-wise uniformity is infeasible (LP) on the fixed-point-free
   involutions of intransitive and imprimitive groups (2n = 6, 8), feasible
   for S_2n; primitive non-alternating groups are reported (they are killed
   only asymptotically, by order).
3. Threshold n1 where 50 (2n)^sqrt(2n) < (theta/C)^(q/(q-1)) m^n.
"""
import itertools, math
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog


def matchings(pts):
    pts = list(pts)
    if not pts:
        yield ()
        return
    a = pts[0]
    for i in range(1, len(pts)):
        b = pts[i]
        rest = pts[1:i] + pts[i + 1:]
        for m in matchings(rest):
            yield ((a, b),) + m


def edges(N):
    return list(itertools.combinations(range(N), 2))


def check_switching():
    for N in (4, 6, 8):
        E = edges(N)
        idx = {e: i for i, e in enumerate(E)}
        Ms = list(matchings(range(N)))
        A = np.zeros((len(Ms), len(E)))
        for r, M in enumerate(Ms):
            for e in M:
                A[r, idx[e]] = 1
        # w with A w constant: A w - c 1 = 0, unknowns (w, c)
        B = np.hstack([A, -np.ones((len(Ms), 1))])
        dim = B.shape[1] - np.linalg.matrix_rank(B)
        assert dim == N, (N, dim)
        print(f"switching N={N}: solution space dim {dim} == N")
        if N <= 6:
            sols = []
            for mask in range(1 << len(E)):
                w = [(mask >> i) & 1 for i in range(len(E))]
                vals = {sum(w[idx[e]] for e in M) for M in Ms}
                if len(vals) == 1:
                    sols.append(frozenset(E[i] for i in range(len(E)) if w[i]))
            allE = frozenset(E)
            expected = {frozenset(), allE}
            for v in range(N):
                star = frozenset(e for e in E if v in e)
                expected |= {star, allE - star}
            assert set(sols) == expected, (N, len(sols), len(expected))
            print(f"switching N={N}: {len(sols)} 0/1 solutions = empty/complete/stars/co-stars")


def compose(p, q):  # (p o q)(x) = p[q[x]]
    return tuple(p[x] for x in q)


def closure(gens, N):
    e = tuple(range(N))
    seen = {e}
    frontier = [e]
    while frontier:
        new = []
        for g in frontier:
            for s in gens:
                h = compose(s, g)
                if h not in seen:
                    seen.add(h)
                    new.append(h)
        frontier = new
    return seen


def perm_from_cycles(N, cycles):
    p = list(range(N))
    for c in cycles:
        for i in range(len(c)):
            p[c[i]] = c[(i + 1) % len(c)]
    return tuple(p)


def fpf_matchings(G, N):
    out = set()
    for g in G:
        if all(g[x] != x for x in range(N)) and all(g[g[x]] == x for x in range(N)):
            out.add(tuple(sorted(tuple(sorted((x, g[x]))) for x in range(N) if x < g[x])))
    return sorted(out)


def two_wise_feasible(Ms, N):
    E = edges(N)
    rows, rhs = [], []
    for e in E:
        rows.append([1.0 if e in M else 0.0 for M in Ms])
        rhs.append(1.0 / (N - 1))
    for e, f in itertools.combinations(E, 2):
        if set(e) & set(f):
            continue
        rows.append([1.0 if (e in M and f in M) else 0.0 for M in Ms])
        rhs.append(1.0 / ((N - 1) * (N - 3)))
    rows.append([1.0] * len(Ms))
    rhs.append(1.0)
    res = linprog(np.zeros(len(Ms)), A_eq=np.array(rows), b_eq=np.array(rhs),
                  bounds=[(0, None)] * len(Ms), method="highs")
    return res.status == 0


def check_groups():
    cases = []
    # degree 6
    cases.append(("S6", 6, [perm_from_cycles(6, [(0, 1)]), perm_from_cycles(6, [(0, 1, 2, 3, 4, 5)])], True))
    cases.append(("S3 wr S2 (imprimitive, blocks of 3)", 6,
                  [perm_from_cycles(6, [(0, 1)]), perm_from_cycles(6, [(0, 1, 2)]),
                   perm_from_cycles(6, [(0, 3), (1, 4), (2, 5)])], False))
    cases.append(("S2 wr S3 (imprimitive, blocks of 2)", 6,
                  [perm_from_cycles(6, [(0, 1)]), perm_from_cycles(6, [(0, 2), (1, 3)]),
                   perm_from_cycles(6, [(0, 2, 4), (1, 3, 5)])], False))
    cases.append(("S4 x S2 (intransitive)", 6,
                  [perm_from_cycles(6, [(0, 1)]), perm_from_cycles(6, [(0, 1, 2, 3)]),
                   perm_from_cycles(6, [(4, 5)])], False))
    # PGL(2,5) on the projective line F5 u {inf}: x->x+1, x->2x, x->-1/x
    inf = 5
    def mob(f):
        return tuple(f(x) for x in range(6))
    t = mob(lambda x: inf if x == inf else (x + 1) % 5)
    d = mob(lambda x: inf if x == inf else (2 * x) % 5)
    s = mob(lambda x: 0 if x == inf else (inf if x == 0 else (-pow(x, 3, 5)) % 5))
    cases.append(("PGL(2,5) (primitive, order 120)", 6, [t, d, s], None))
    # degree 8
    cases.append(("S8", 8, [perm_from_cycles(8, [(0, 1)]), perm_from_cycles(8, [tuple(range(8))])], True))
    cases.append(("S4 wr S2 (imprimitive)", 8,
                  [perm_from_cycles(8, [(0, 1)]), perm_from_cycles(8, [(0, 1, 2, 3)]),
                   perm_from_cycles(8, [(0, 4), (1, 5), (2, 6), (3, 7)])], False))
    cases.append(("S2 wr S4 (imprimitive, stabilizer of a matching)", 8,
                  [perm_from_cycles(8, [(0, 1)]), perm_from_cycles(8, [(0, 2), (1, 3)]),
                   perm_from_cycles(8, [(0, 2, 4, 6), (1, 3, 5, 7)])], False))
    cases.append(("S6 x S2 (intransitive)", 8,
                  [perm_from_cycles(8, [(0, 1)]), perm_from_cycles(8, [tuple(range(6))]),
                   perm_from_cycles(8, [(6, 7)])], False))
    # AGL(3,2) on F_2^3: translations, GL(3,2) generators
    def vec(i):
        return [(i >> k) & 1 for k in range(3)]
    def num(v):
        return sum(b << k for k, b in enumerate(v))
    def lin(Mx):
        return tuple(num([sum(Mx[r][c] * vec(i)[c] for c in range(3)) % 2 for r in range(3)]) for i in range(8))
    tr = tuple(i ^ 1 for i in range(8))
    g1 = lin([[1, 1, 0], [0, 1, 0], [0, 0, 1]])
    g2 = lin([[0, 0, 1], [1, 0, 0], [0, 1, 0]])
    cases.append(("AGL(3,2) (primitive, order 1344)", 8, [tr, g1, g2], None))
    # M12 on 12 points (5-transitive): a proper primitive group that DOES carry an
    # exact 2-wise uniform law, so the order step of the proof is necessary.
    c12 = lambda cyc: perm_from_cycles(12, [tuple(x - 1 for x in cy) for cy in cyc])
    m12 = [c12([(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)]), c12([(3, 7, 11, 8), (4, 10, 5, 6)]),
           c12([(1, 12), (2, 11), (3, 6), (4, 8), (5, 9), (7, 10)])]
    cases.append(("M12 (primitive, 5-transitive, order 95040)", 12, m12, True))
    for name, N, gens, expect in cases:
        G = closure(gens, N)
        Ms = fpf_matchings(G, N)
        feas = two_wise_feasible(Ms, N)
        print(f"{name}: |G|={len(G)}, fpf involutions={len(Ms)}, exact 2-wise uniform law exists: {feas}")
        if expect is not None:
            assert feas == expect, name
        if name.startswith("AGL"):
            assert len(G) == 1344
        if name.startswith("PGL(2,5)"):
            assert len(G) == 120
        if name.startswith("M12"):
            assert len(G) == 95040


def threshold():
    expected = {(2, 2, 10): 202, (2, 2, 1000): 233, (3, 4, 100): 77, (5, 2, 10**6): 83}

    def holds(m, q, C, n):
        theta = (n + 1) ** (-(m - 1))
        lhs = math.log(50) + math.sqrt(2 * n) * math.log(2 * n)
        rhs = (q / (q - 1)) * math.log(theta / C) + n * math.log(m)
        return lhs < rhs

    for (m, q, C), n_exp in expected.items():
        n1 = next(n for n in range(3, 100000) if holds(m, q, C, n))
        assert n1 == n_exp, (m, q, C, n1)
        assert all(holds(m, q, C, n) for n in range(n1, 20001))
        qp = q / (q - 1)
        deriv = math.log(m) - qp * (m - 1) / (n1 + 1) - (math.log(2 * n1) + 2) / math.sqrt(2 * n1)
        assert deriv > 0
        print(f"m={m} q={q} C={C}: first crossing n1 = {n1}, holds up to 20000, slope {deriv:.3f} > 0")


if __name__ == "__main__":
    check_switching()
    check_groups()
    threshold()
    print("ALL CHECKS PASSED")
