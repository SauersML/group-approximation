#!/usr/bin/env python3
"""Coefficient rigidity of Rips--Segev / Steenbock non-unique-product witnesses.

Setting (Steenbock, arXiv:1307.0981, Sec. "Generalized Rips-Segev graphs"):
  A = disjoint union over lines i = 0..K-1 of {c_i a^l : 0 <= l < C_i},
  B = {1, a, b, ab}.
Product positions: (i,l)*1 -> v(i,l), (i,l)*a -> v(i,l+1),
                   (i,l)*b -> w(i,l), (i,l)*ab -> w(i,l+1).
Step 1 glues each w-endpoint w(i,0), w(i,C_i) to a distinct v(j,I), 0<=I<=C_j.
Step 2 glues each v-endpoint not hit in Step 1 to a distinct interior w(l,O).

ENCODED PATTERN MODEL: two products coincide iff their positions are glued.
(This is exact in G(Gamma) under hypothesis EE of
research/rips-segev-witness-pairs-carry-no-zero-divisors.md.)

For beta = 1 + x a + y b + z ab over F_p, the map alpha -> alpha*beta on
alpha supported in A is a linear map F_p^A -> F_p^{vertex classes}.
The script computes its kernel for every (x,y,z) and reports
  * kernel dimension,
  * whether a kernel vector of FULL support (supp alpha = A) exists,
  * the largest kernel support.

Predictions from the proof:
  (P1) z != xy and a free index exists  =>  no full-support kernel vector.
  (P2) z == xy                          =>  the pattern kernel may be nonzero,
       but the group-level argument ((1+xa),(1+yb) are non-zero-divisors)
       kills it; the script flags these rows as 'factorizable'.
Calibration (mode 'calib'): the same linear algebra in the finite abelian
group Z/n x Z/m must FIND zero divisors (torsion), e.g. alpha = sum a^i.

Usage: rs_witness_nullspace.py [--p P] [--trials T] [--seed S] [--maxK K] [--maxC C]
Single-threaded, pure python, small memory.
"""
import argparse
import itertools
import random


def rank_nullspace_mod(rows, ncols, p):
    """Return a basis of the kernel {u : M u = 0} over F_p, M given by rows."""
    M = [list(r) for r in rows]
    pivcols = []
    r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, len(M)):
            if M[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(v * inv) % p for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(vi - f * vr) % p for vi, vr in zip(M[i], M[r])]
        pivcols.append(c)
        r += 1
        if r == len(M):
            break
    free = [c for c in range(ncols) if c not in set(pivcols)]
    basis = []
    for fc in free:
        u = [0] * ncols
        u[fc] = 1
        for i, pc in enumerate(pivcols):
            u[pc] = (-M[i][fc]) % p
        basis.append(u)
    return basis


def kernel_support_stats(basis, ncols, p, enum_limit=6):
    """Union support of kernel; full-support existence (exact if dim small)."""
    union = set()
    for u in basis:
        union |= {c for c in range(ncols) if u[c]}
    d = len(basis)
    full = None
    if d == 0:
        full = False
    elif d <= enum_limit and p ** d <= 50000:
        full = False
        for coeffs in itertools.product(range(p), repeat=d):
            if not any(coeffs):
                continue
            v = [0] * ncols
            for cf, u in zip(coeffs, basis):
                if cf:
                    v = [(vi + cf * ui) % p for vi, ui in zip(v, u)]
            if all(v):
                full = True
                break
    return d, len(union), full


class UF:
    def __init__(self):
        self.par = {}

    def find(self, x):
        self.par.setdefault(x, x)
        while self.par[x] != x:
            self.par[x] = self.par[self.par[x]]
            x = self.par[x]
        return x

    def union(self, x, y):
        self.par[self.find(x)] = self.find(y)


def random_rs_graph(K, Cs, rng):
    """Random Steps 1-2 gluing; returns (uf, free_indices) or None."""
    uf = UF()
    vtargets = [("v", j, I) for j in range(K) for I in range(Cs[j] + 1)]
    wends = [("w", i, 0) for i in range(K)] + [("w", i, Cs[i]) for i in range(K)]
    if len(vtargets) < len(wends):
        return None
    chosen = rng.sample(vtargets, len(wends))
    for w, v in zip(wends, chosen):
        uf.union(w, v)
    hit = set(chosen)
    vends = [("v", i, 0) for i in range(K)] + [("v", i, Cs[i]) for i in range(K)]
    loose = [v for v in vends if v not in hit]
    winter = [("w", l, O) for l in range(K) for O in range(1, Cs[l])]
    if len(winter) < len(loose):
        return None
    chosen2 = rng.sample(winter, len(loose))
    for v, w in zip(loose, chosen2):
        uf.union(v, w)
    glued = set(chosen) | set(wends) | set(loose) | set(chosen2)
    free = [(i, l) for i in range(K) for l in range(1, Cs[i])
            if ("v", i, l) not in glued and ("w", i, l) not in glued]
    return uf, free


def pattern_rows(K, Cs, uf, beta):
    x1, xa, xb, xab = beta
    cols = [(i, l) for i in range(K) for l in range(Cs[i])]
    colidx = {c: n for n, c in enumerate(cols)}
    rows = {}
    for (i, l), n in colidx.items():
        for pos, cf in ((("v", i, l), x1), (("v", i, l + 1), xa),
                        (("w", i, l), xb), (("w", i, l + 1), xab)):
            key = uf.find(pos)
            rows.setdefault(key, [0] * len(cols))
            rows[key][n] += cf
    return list(rows.values()), len(cols)


def run_rs(args):
    rng = random.Random(args.seed)
    p = args.p
    betas = [(1, x, y, z) for x in range(1, p) for y in range(1, p) for z in range(1, p)]
    summary = {"graphs": 0, "free": 0, "P1_violations": 0,
               "nonfact_nonzero_kernel": 0, "nonfact_rows": 0,
               "fact_rows": 0, "fact_nonzero_kernel": 0, "fact_full": 0,
               "nonfact_full_nofree": 0, "full_undetermined": 0,
               "fact_graphs_nonzero_kernel": 0}
    for _ in range(args.trials):
        K = rng.randint(1, args.maxK)
        Cs = [rng.randint(2, args.maxC) for _ in range(K)]
        g = random_rs_graph(K, Cs, rng)
        if g is None:
            continue
        uf, free = g
        summary["graphs"] += 1
        fact_kernel_here = False
        if free:
            summary["free"] += 1
        for beta in betas:
            rows, n = pattern_rows(K, Cs, uf, beta)
            basis = rank_nullspace_mod(rows, n, p)
            d, supp, full = kernel_support_stats(basis, n, p)
            fact = (beta[3] - beta[1] * beta[2]) % p == 0
            if d > 0 and full is None:
                summary["full_undetermined"] += 1
            if fact:
                summary["fact_rows"] += 1
                summary["fact_nonzero_kernel"] += d > 0
                summary["fact_full"] += bool(full)
                fact_kernel_here |= d > 0
            else:
                summary["nonfact_rows"] += 1
                summary["nonfact_nonzero_kernel"] += d > 0
                if full and not free:
                    summary["nonfact_full_nofree"] += 1
                if free and full:
                    summary["P1_violations"] += 1
                    print("P1 VIOLATION", K, Cs, beta, d)
        summary["fact_graphs_nonzero_kernel"] += fact_kernel_here
    print("RS pattern model over F_%d (trials=%d seed=%d maxK=%d maxC=%d):"
          % (p, args.trials, args.seed, args.maxK, args.maxC), summary)
    return summary


def run_calib(p):
    """Finite abelian Z/n x Z/m: zero divisors with supp beta in {1,a,b,ab} exist."""
    found = 0
    for n, m in ((2, 1), (3, 1), (2, 2), (3, 2), (4, 3)):
        elems = [(s, t) for s in range(n) for t in range(m)]
        idx = {e: k for k, e in enumerate(elems)}
        for beta in [(1, x, y, z) for x in range(p) for y in range(p) for z in range(p)]:
            rows = [[0] * len(elems) for _ in elems]
            for (s, t), k in idx.items():
                for (ds, dt), cf in (((0, 0), beta[0]), ((1, 0), beta[1]),
                                     ((0, 1), beta[2]), ((1, 1), beta[3])):
                    rows[idx[((s + ds) % n, (t + dt) % m)]][k] += cf
            if rank_nullspace_mod(rows, len(elems), p):
                found += 1
    print("calibration (finite abelian, torsion): betas with nonzero annihilator:", found)
    return found


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--p", type=int, default=3)
    ap.add_argument("--trials", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--maxK", type=int, default=3)
    ap.add_argument("--maxC", type=int, default=9)
    a = ap.parse_args()
    assert run_calib(a.p) > 0, "calibration failed: method finds no torsion zero divisors"
    run_rs(a)
