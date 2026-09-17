#!/usr/bin/env python3
"""Gap argument check for research/rips-segev-witness-supports-carry-no-zero-divisors.md.

Model: generalized Rips--Segev gluings (Steenbock arXiv:1307.0981, Steps 1-2) in the exact encoded
pattern model (two products coincide iff their positions are glued).  Distinguished positions of line i:
0, C_i, Step-1 targets (v glued) and Step-2 targets (w glued).  We only keep gluings in which at most
`--adjacent` pairs of distinguished positions on a common line are at distance 1.

For EVERY beta = p + x a + y b + z ab in F_q^4 \\ {0} and EVERY alpha supported in A (the whole kernel of
alpha -> alpha*beta is computed) the script checks the prediction:

  (G) if p z - x y != 0, every kernel vector has support contained in the set of indices d with d and d+1
      both distinguished.  With no adjacent pair the kernel is 0; with one adjacent pair the support is
      at most one element.

Rank-one beta (p z = x y) are reported separately; there the group-level argument is the factorization
(u + v a)(s + t b), not linear algebra.
Calibration: with --adjacent large (unrestricted gluings) the script must find non-rank-one beta with a
kernel vector of support >= 2 in some gluing without spacing, showing that the spacing hypothesis is used.
"""
import argparse
import itertools
import random


def nullspace_mod(rows, ncols, p):
    M = [list(r) for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        pr = next((i for i in range(r, len(M)) if M[i][c] % p), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(v * inv) % p for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    free = [c for c in range(ncols) if c not in set(piv)]
    basis = []
    for fc in free:
        u = [0] * ncols
        u[fc] = 1
        for i, pc in enumerate(piv):
            u[pc] = (-M[i][fc]) % p
        basis.append(u)
    return basis


def random_gluing(rng, K, Cs):
    parent = {}

    def find(x):
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    vt = [("v", j, I) for j in range(K) for I in range(Cs[j] + 1)]
    wends = [("w", i, e) for i in range(K) for e in (0, Cs[i])]
    ch1 = rng.sample(vt, len(wends))
    for w, v in zip(wends, ch1):
        parent[find(w)] = find(v)
    hit = set(ch1)
    loose = [("v", i, e) for i in range(K) for e in (0, Cs[i]) if ("v", i, e) not in hit]
    wint = [("w", l, O) for l in range(K) for O in range(1, Cs[l])]
    if len(wint) < len(loose):
        return None
    ch2 = rng.sample(wint, len(loose))
    for v, w in zip(loose, ch2):
        parent[find(v)] = find(w)
    dist = [set([0, Cs[i]]) for i in range(K)]
    for (_, j, I) in ch1:
        dist[j].add(I)
    for (_, l, O) in ch2:
        dist[l].add(O)
    return find, dist


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--p", type=int, default=3)
    ap.add_argument("--trials", type=int, default=400)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--maxK", type=int, default=3)
    ap.add_argument("--maxC", type=int, default=12)
    ap.add_argument("--adjacent", type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    p = a.p
    betas = [b for b in itertools.product(range(p), repeat=4) if any(b)]
    st = dict(graphs=0, violations=0, nonrank1_rows=0, nonrank1_nonzero_kernel=0,
              rank1_rows=0, rank1_nonzero_kernel=0, nonrank1_support_ge2=0)
    tries = 0
    while st["graphs"] < a.trials and tries < 200 * a.trials:
        tries += 1
        K = rng.randint(1, a.maxK)
        Cs = [rng.randint(2, a.maxC) for _ in range(K)]
        g = random_gluing(rng, K, Cs)
        if g is None:
            continue
        find, dist = g
        adj = [(i, d) for i in range(K) for d in dist[i] if d + 1 in dist[i]]
        if len(adj) > a.adjacent:
            continue
        st["graphs"] += 1
        cols = [(i, l) for i in range(K) for l in range(Cs[i])]
        allowed = {(i, d) for (i, d) in adj if d < Cs[i]}
        for beta in betas:
            pp, x, y, z = beta
            rows = {}
            for n, (i, l) in enumerate(cols):
                for pos, cf in ((("v", i, l), pp), (("v", i, l + 1), x),
                                (("w", i, l), y), (("w", i, l + 1), z)):
                    if cf:
                        rows.setdefault(find(pos), [0] * len(cols))[n] += cf
            basis = nullspace_mod(list(rows.values()), len(cols), p)
            rank1 = (pp * z - x * y) % p == 0
            union = {cols[c] for u in basis for c in range(len(cols)) if u[c]}
            if rank1:
                st["rank1_rows"] += 1
                st["rank1_nonzero_kernel"] += bool(basis)
            else:
                st["nonrank1_rows"] += 1
                st["nonrank1_nonzero_kernel"] += bool(basis)
                if len(union) >= 2:
                    st["nonrank1_support_ge2"] += 1
                if not union <= allowed:
                    st["violations"] += 1
    print("F_%d trials=%d seed=%d maxK=%d maxC=%d adjacent<=%d:" %
          (p, a.trials, a.seed, a.maxK, a.maxC, a.adjacent), st)


if __name__ == "__main__":
    main()
