#!/usr/bin/env python3
"""Folded DKKMS host at l = 1, beta = 0, with DKKMS legitimacy (a) and (b).

Checks for research/folded-dkkms-line-hosts-have-uniform-spectral-gap.md:

  (1) Lemma 4.1 classes at l = 1 are exactly the fibres of S = supp(r), r the
      weight-<=1-per-block representative of v mod H_U.  Checked against the
      union-find closure of the paper's defining relation
          span(v) + H_U + H_U' = span(v') + H_U + H_U'
      over all pairs of A-vertices whose tuples share a variable (disjoint
      tuples are never related).  With legitimacy (b) the two partitions agree
      exactly; without (b) (disjointness only, as in
      ugc-akkstv-regularize-2026-09-17/dkkms_folded_gap_large.py) they need not.
  (2) lambda_2 = 1 - sigma_2 of the class-versus-tuple bipartite matrix, compared
      with the theorem's bound 1 - sqrt(rho_k + 2 delta), rho_k = (3/4)/(1-4^-k),
      and with its n -> infinity value 1 - sqrt(rho_k).
Seeded; runs in a few minutes on one core.
"""
import itertools
import random
from collections import defaultdict

import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import svds


def regular_3lin(n, D, rng):
    for _ in range(100000):
        stubs = [v for v in range(n) for _ in range(D)]
        rng.shuffle(stubs)
        eqs = [tuple(sorted(stubs[3 * i:3 * i + 3])) for i in range(len(stubs) // 3)]
        if not all(len(set(e)) == 3 for e in eqs):
            continue
        if all(len(set(a) & set(b)) <= 1 for a, b in itertools.combinations(eqs, 2)):
            return eqs
    raise RuntimeError("no regular system")


def legit_tuples(EQ, k, cond_b=True):
    eqs_of = defaultdict(list)
    for j, e in enumerate(EQ):
        for x in e:
            eqs_of[x].append(j)
    joined = set()  # pairs of variables that appear together in some equation
    for e in EQ:
        for x, y in itertools.permutations(e, 2):
            joined.add((x, y))
    out = []
    for c in itertools.combinations(range(len(EQ)), k):
        vs = [set(EQ[i]) for i in c]
        if len(set().union(*vs)) != 3 * k:
            continue
        if cond_b and any((x, y) in joined for a, b in itertools.combinations(vs, 2)
                          for x in a for y in b):
            continue
        out.append(c)
    return out


def span_mask(vecs):
    s = {0}
    for v in vecs:
        s |= {x ^ v for x in s}
    return s


def check_classes(EQ, tuples):
    """Union-find of the defining relation versus the S-fibres."""
    A, key = [], []
    H = {}
    for U in tuples:
        hs = [sum(1 << x for x in EQ[i]) for i in U]
        H[U] = span_mask(hs)
        XU = sum(hs)
        for v in range(1, 1 << (3 * len(U))):
            # enumerate subsets of X_U via bits of the 3k variables
            vars_ = [x for i in U for x in EQ[i]]
            w = sum(1 << vars_[j] for j in range(3 * len(U)) if v >> j & 1)
            if w in H[U]:
                continue
            S = []
            for i in U:
                pat = [(w >> x) & 1 for x in EQ[i]]
                if sum(pat) in (1, 2):
                    odd = pat.index(1) if sum(pat) == 1 else pat.index(0)
                    S.append(EQ[i][odd])
            A.append((U, w))
            key.append(frozenset(S))
    par = list(range(len(A)))

    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a

    byU = defaultdict(list)
    for idx, (U, w) in enumerate(A):
        byU[U].append(idx)
    vset = {U: set(x for i in U for x in EQ[i]) for U in tuples}
    in_h = set()  # pairs where some v of U1 lies in H_U1 + H_U2 (never under (b))
    pairs = [(U, U) for U in tuples] + list(itertools.combinations(tuples, 2))
    for U1, U2 in pairs:
        if not vset[U1] & vset[U2]:
            continue
        HH = span_mask([sum(1 << x for x in EQ[i]) for i in set(U1) | set(U2)])
        for a in byU[U1]:
            wa = A[a][1]
            if wa in HH:
                in_h.add((U1, U2))
                continue
            sa = frozenset(wa ^ h for h in HH)
            for b in byU[U2]:
                if A[b][1] in sa:
                    # w_b in w_a + HH and w_a notin HH: span(w_b)+HH == span(w_a)+HH
                    ra, rb = find(a), find(b)
                    if ra != rb:
                        par[ra] = rb
    comp = defaultdict(set)
    for idx in range(len(A)):
        comp[find(idx)].add(key[idx])
    fib = defaultdict(set)
    for idx in range(len(A)):
        fib[key[idx]].add(find(idx))
    agree = all(len(s) == 1 for s in comp.values()) and all(len(s) == 1 for s in fib.values())
    return agree and not in_h, len(comp), len(fib), len(in_h)


def gap_l1(EQ, tuples, k):
    col = {U: j for j, U in enumerate(tuples)}
    row = {}
    rows, cols = [], []
    for U in tuples:
        for m in range(1, k + 1):
            for blocks in itertools.combinations(U, m):
                for S in itertools.product(*[EQ[i] for i in blocks]):
                    r = row.setdefault(frozenset(S), len(row))
                    rows.append(r)
                    cols.append(col[U])
    M = sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(len(row), len(tuples)))
    # weight of edge (S, U) is #v in U with key S = 2^k, constant: drop it
    r = np.asarray(M.sum(1)).ravel()
    c = np.asarray(M.sum(0)).ravel()
    N = (sp.diags(1 / np.sqrt(r)) @ M @ sp.diags(1 / np.sqrt(c))).tocsc()
    s = np.sort(svds(N, k=3, return_singular_vectors=False, tol=1e-10))[::-1]
    return 1 - s[1]


if __name__ == "__main__":
    rng = random.Random(20260918)
    print("(1) Lemma 4.1 classes = S-fibres at l = 1")
    for n, D, k in [(24, 2, 2), (30, 2, 2), (24, 2, 3)]:
        EQ = regular_3lin(n, D, rng)
        for cb in (True, False):
            T = legit_tuples(EQ, k, cond_b=cb)
            agree, nc, nf, nh = check_classes(EQ, T)
            print(f"  n={n} D={D} k={k} legit(b)={cb}: tuples={len(T)} "
                  f"union-find classes={nc} S-fibres={nf} pairs with v in H_U+H_U'={nh} "
                  f"agree={agree}")
    print("(2) lambda_2 = 1 - sigma_2 versus 1 - sqrt(rho_k)")
    for n, D, k in [(30, 2, 2), (60, 2, 2), (120, 2, 2), (240, 2, 2),
                    (30, 2, 3), (60, 2, 3), (90, 2, 3)]:
        EQ = regular_3lin(n, D, rng)
        T = legit_tuples(EQ, k)
        rho = 0.75 / (1 - 4.0 ** (-k))
        g = gap_l1(EQ, T, k)
        print(f"  n={n} D={D} k={k}: tuples={len(T)} lambda_2={g:.4f} "
              f"limit bound={1 - np.sqrt(rho):.4f} ok={g >= 1 - np.sqrt(rho) - 1e-9}")
