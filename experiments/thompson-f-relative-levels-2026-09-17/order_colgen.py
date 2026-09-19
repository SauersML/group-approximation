"""Order-only LP by column generation with exact MILP pricing.

Tie-free relative laws: a law on total orders of the middle leaves (the ties-free part of any
relative-level law, with arbitrarily many relative levels / scales).  The observation kept for
word s is perm_s = the order of its middle positions by the maxima of their pieces (a function of
Obs_s, so equality of the laws of perm_s is necessary for zero defect).

Master LP: min sum_(s>=1, p) |q_s(p) - q_0(p)| over laws on the realisable vectors found so far.
Pricing:   max over total orders of  sum_(s>=1) (y[s, perm_s] - y[s, perm_0]) + z, as a MILP on
           leaf-order variables (transitive tournament), exact (HiGHS, integral).
The loop stops when the MILP proves no column has negative reduced cost, so the final value is
the exact LP optimum over all total orders.

Usage: python3 order_colgen.py m d
"""
import itertools
import sys

import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog, milp, LinearConstraint, Bounds

from relative_level_lp import setup

PERMS = None


def perm_of(order_rank, pieces):
    """order_rank[v] = rank (higher = larger). Return positions sorted by decreasing piece max."""
    H = [max(order_rank[v] for v in P) for P in pieces]
    return tuple(sorted(range(len(pieces)), key=lambda j: -H[j]))


class Pricer:
    def __init__(self, L, n):
        self.L, self.n = L, n
        ns, k = len(L), len(L[0])
        self.ns, self.k = ns, k
        idx = {}

        def var(key):
            if key not in idx:
                idx[key] = len(idx)
            return idx[key]

        rows = []  # (dict coef, lo, hi)
        # y[u,v] = [u above v] for u != v, y[u,v] + y[v,u] = 1, transitivity
        for u, v in itertools.combinations(range(n), 2):
            rows.append(({var(("y", u, v)): 1, var(("y", v, u)): 1}, 1, 1))
        for u, v, w in itertools.permutations(range(n), 3):
            rows.append(({var(("y", u, v)): 1, var(("y", v, w)): 1, var(("y", u, w)): -1}, -np.inf, 1))
        # z[P,Q] = [max P > max Q] for disjoint leaf sets P, Q in one word
        zkeys = {}
        for s in range(ns):
            for a, b in itertools.permutations(range(k), 2):
                P, Q = L[s][a], L[s][b]
                if (P, Q) in zkeys:
                    continue
                zq = var(("z", P, Q))
                zkeys[(P, Q)] = zq
                avars = []
                for u in P:
                    au = var(("a", u, Q))
                    avars.append(au)
                    for v in Q:  # au <= y[u,v]
                        rows.append(({au: 1, var(("y", u, v)): -1}, -np.inf, 0))
                    # au >= sum y - (|Q|-1)
                    c = {au: 1}
                    for v in Q:
                        c[var(("y", u, v))] = -1
                    rows.append((c, -(len(Q) - 1), np.inf))
                # zq = OR avars (au are disjoint events: exactly one u is the max of P ∪ ... ;
                # use zq >= au and zq <= sum au)
                for au in avars:
                    rows.append(({zq: 1, au: -1}, 0, np.inf))
                c = {zq: 1}
                for au in avars:
                    c[au] = -1
                rows.append((c, -np.inf, 0))
        # t[s,p] = [perm_s = p]
        global PERMS
        PERMS = list(itertools.permutations(range(k)))
        for s in range(ns):
            c = {}
            for p in PERMS:
                t = var(("t", s, p))
                c[t] = 1
                for x in range(k):
                    for y_ in range(x + 1, k):
                        # p[x] above p[y_]
                        rows.append(({t: 1, zkeys[(L[s][p[x]], L[s][p[y_]])]: -1}, -np.inf, 0))
            rows.append((c, 1, 1))
        self.idx = idx
        N = len(idx)
        ri, ci, vv, lo, hi = [], [], [], [], []
        for r, (c, l, h) in enumerate(rows):
            for j, a in c.items():
                ri.append(r), ci.append(j), vv.append(a)
            lo.append(l), hi.append(h)
        self.A = sp.csr_matrix((vv, (ri, ci)), shape=(len(rows), N))
        self.lo, self.hi = np.array(lo, float), np.array(hi, float)
        self.N = N

    def price(self, weight):
        """weight[(s,p)] -> maximise sum weight * t. Returns (value, rank vector)."""
        cost = np.zeros(self.N)
        for (s, p), w in weight.items():
            cost[self.idx[("t", s, p)]] -= w
        res = milp(cost, constraints=LinearConstraint(self.A, self.lo, self.hi),
                   integrality=np.ones(self.N), bounds=Bounds(0, 1),
                   options={"disp": False, "mip_rel_gap": 0})
        x = np.round(res.x).astype(int)
        n = self.n
        rank = [sum(x[self.idx[("y", u, v)]] for v in range(n) if v != u) for u in range(n)]
        return -res.fun, rank


def master(vectors, ns):
    rowkey = {}
    ri, ci, vv = [], [], []
    for c, vec in enumerate(vectors):
        for s in range(1, ns):
            if vec[s] == vec[0]:
                continue
            for key, sg in (((s, vec[s]), 1.0), ((s, vec[0]), -1.0)):
                r = rowkey.setdefault(key, len(rowkey))
                ri.append(r), ci.append(c), vv.append(sg)
    R, N = len(rowkey), len(vectors)
    A = sp.csr_matrix((vv, (ri, ci)), shape=(R, N))
    Aeq = sp.vstack([sp.hstack([A, -sp.eye(R), sp.eye(R)]),
                     sp.hstack([sp.csr_matrix(np.ones((1, N))), sp.csr_matrix((1, 2 * R))])]).tocsc()
    beq = np.zeros(R + 1)
    beq[-1] = 1
    cost = np.concatenate([np.zeros(N), np.ones(2 * R)])
    res = linprog(cost, A_eq=Aeq, b_eq=beq, bounds=(0, None), method="highs")
    return res, rowkey


def run(m, d, rounds=2000, verbose=True):
    S, LV, L = setup(m, d)
    n, ns = len(LV), len(S)
    pr = Pricer(L, n)
    rng = np.random.default_rng(0)
    vectors = set()
    for _ in range(200):
        rk = list(rng.permutation(n))
        vectors.add(tuple(perm_of(rk, L[s]) for s in range(ns)))
    vectors = sorted(vectors)
    for rnd in range(rounds):
        res, rowkey = master(vectors, ns)
        R = len(rowkey)
        y = res.eqlin.marginals
        yk, z = y[:R], y[R]
        # reduced cost of a column = -z - sum_s>=1 (y[s,perm_s] - y[s,perm_0]) ; want < 0
        # i.e. maximise sum_s>=1 y[s,perm_s] - sum_s>=1 y[s,perm_0]  > -z
        weight = {}
        for (s, p), r in rowkey.items():
            weight[(s, p)] = weight.get((s, p), 0.0) + yk[r]
            weight[(0, p)] = weight.get((0, p), 0.0) - yk[r]
        val, rank = pr.price(weight)
        vec = tuple(perm_of(rank, L[s]) for s in range(ns))
        red = -z - val
        if verbose:
            print(f"round {rnd}: cols={len(vectors)} value={res.fun:.6g} best reduced cost={red:.3g}",
                  flush=True)
        if red > -1e-7 or vec in vectors:
            break
        vectors.append(vec)
    p = res.x[:len(vectors)]
    return res.fun, vectors, p, S, L


if __name__ == "__main__":
    m, d = int(sys.argv[1]), int(sys.argv[2])
    val, vectors, p, S, L = run(m, d)
    print(f"FINAL (m,d)=({m},{d}) order-only LP exact min violation = {val:.6g}")
    for c in np.argsort(-p)[:12]:
        if p[c] > 1e-9:
            print(f"  p={p[c]:.4f} perms={vectors[c]}")
