#!/usr/bin/env python3
"""Folded versus unfolded spectral gap of DKKMS 2-to-1 hosts on a sparse 3LIN.

Same edge process as dkkms_host_gap.py (TR16-198 Sec 4.2 as quoted in
dkkms-2to1-instances-satisfy-selector-decoding-hypotheses), but on a random
D-regular 3-uniform system with many variables, so that two k-tuples rarely
overlap (the regime of the paper, where n >> k). A-vertices are stored after
the within-U merge (U, K = L + H_U); this is the finest folding and every
Lemma 4.1 class is a union of these blocks.

Foldings reported:
  unfolded   the host on A = {(U,L)}                  (no merging)
  within-U   blocks (U, L + H_U)                       (lower bound for folded)
  canonical  fibres of (U,K) -> R, R the least-support admissible l-space in K
             (ties lexicographic). Each fibre lies in {(U,L): L+H_U = R+H_U}.
  exact      fraction of A-mass whose fibre equals the whole Lemma 4.1 set
             {(U',L') in A : L'+H_U' = R+H_U'}; near 1 means the canonical
             fibres are the paper's classes on this instance.
lambda_2 = 1 - sigma_2 of the normalized bipartite matrix (sparse SVD).
"""
import itertools
import random
import sys
from collections import defaultdict

import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import svds


def regular_3lin(n, D, rng):
    for _ in range(10000):
        stubs = [v for v in range(n) for _ in range(D)]
        rng.shuffle(stubs)
        eqs = [tuple(sorted(stubs[3 * i:3 * i + 3])) for i in range(len(stubs) // 3)]
        if all(len(set(e)) == 3 for e in eqs) and len(set(eqs)) == len(eqs):
            return eqs
    raise RuntimeError("no simple regular system found")


def span(vecs):
    s = {0}
    for v in vecs:
        s |= {x ^ v for x in s}
    return frozenset(s)


def mask(vars_):
    return sum(1 << v for v in vars_)


SUBS = {}


def subspaces_of(m, dim):
    if (m, dim) in SUBS:
        return SUBS[(m, dim)]
    if dim == 0:
        SUBS[(m, dim)] = [frozenset([0])]
        return SUBS[(m, dim)]
    coords = [i for i in range(m.bit_length()) if m >> i & 1]
    vecs = [sum(1 << coords[j] for j in range(len(coords)) if t >> j & 1)
            for t in range(1, 1 << len(coords))]
    out = set()
    for basis in itertools.combinations(vecs, dim):
        s = span(basis)
        if len(s) == 1 << dim:
            out.add(s)
    SUBS[(m, dim)] = list(out)
    return SUBS[(m, dim)]


def canon_R(K, HU, l):
    best = None
    for b in itertools.combinations(sorted(K - {0}), l):
        R = span(b)
        if len(R) != 1 << l or len(R & HU) != 1:
            continue
        sup = 0
        for v in R:
            sup |= v
        key = (bin(sup).count("1"), tuple(sorted(R)))
        if best is None or key < best:
            best = key
    return frozenset(best[1])


def build(EQ, k, l, beta):
    tuples = [c for c in itertools.combinations(range(len(EQ)), k)
              if len(set().union(*[set(EQ[i]) for i in c])) == 3 * k]
    Aun, Akey, B = {}, {}, {}
    Wun, Wkey = defaultdict(float), defaultdict(float)
    HUs = {}
    for U in tuples:
        XU = mask(v for i in U for v in EQ[i])
        HU = span([mask(EQ[i]) for i in U])
        HUs[U] = HU
        up = defaultdict(list)
        if l > 1:
            for L in subspaces_of(XU, l):
                for basis in itertools.combinations(sorted(L - {0}), l - 1):
                    s = span(basis)
                    if len(s) == 1 << (l - 1):
                        up[s].append(L)
            up = {s: list(set(v)) for s, v in up.items()}
        opts = [[(('e', i), 1 - beta)] + [(('x', v), beta / 3) for v in EQ[i]]
                for i in U]
        for choice in itertools.product(*opts):
            pV = float(np.prod([c[1] for c in choice]))
            if pV == 0:
                continue
            V = tuple(sorted(c[0] for c in choice))
            XV = mask(v for t, a in V for v in (EQ[a] if t == 'e' else [a]))
            Lps = subspaces_of(XV, l - 1)
            for Lp in Lps:
                ups = up[Lp] if l > 1 else subspaces_of(XU, 1)
                for L in ups:
                    if len(L & HU) != 1:
                        continue
                    w = pV / len(Lps) / len(ups)
                    b = B.setdefault((V, Lp), len(B))
                    a = Aun.setdefault((U, L), len(Aun))
                    Wun[(a, b)] += w
                    K = span(list(L | HU))
                    c = Akey.setdefault((U, K), len(Akey))
                    Wkey[(c, b)] += w
    return tuples, HUs, Aun, Akey, B, Wun, Wkey


def gap(W, nA, nB, amap=None):
    rows, cols, vals = [], [], []
    for (a, b), w in W.items():
        rows.append(amap[a] if amap is not None else a)
        cols.append(b)
        vals.append(w)
    nA = (max(amap) + 1) if amap is not None else nA
    M = sp.csr_matrix((vals, (rows, cols)), shape=(nA, nB))
    r = np.asarray(M.sum(1)).ravel()
    c = np.asarray(M.sum(0)).ravel()
    Dr = sp.diags(1 / np.sqrt(np.where(r > 0, r, 1)))
    Dc = sp.diags(1 / np.sqrt(np.where(c > 0, c, 1)))
    N = (Dr @ M @ Dc).tocsc()
    if min(N.shape) <= 3:
        s = np.linalg.svd(N.toarray(), compute_uv=False)
    else:
        s = svds(N, k=3, return_singular_vectors=False, tol=1e-10)
    s = np.sort(s)[::-1]
    return 1 - s[1], nA


def canonical(HUs, Akey, l, Wkey):
    amap = [0] * len(Akey)
    roots = {}
    Rof = {}
    for (U, K), i in Akey.items():
        R = canon_R(K, HUs[U], l)
        Rof[(U, K)] = R
        amap[i] = roots.setdefault(R, len(roots))
    # exactness: is the fibre of R the whole Lemma 4.1 set?
    mass = defaultdict(float)
    for (c, b), w in Wkey.items():
        mass[c] += w
    keyset = set(Akey)
    exact_mass = tot = 0.0
    bad_R = set()
    for R in roots:
        sup = 0
        for v in R:
            sup |= v
        for U, HU in HUs.items():
            XU = 0
            for h in HU:
                XU |= h
            if sup & ~XU or len(R & HU) != 1:
                continue
            K = span(list(R | HU))
            if (U, K) in keyset and Rof[(U, K)] != R:
                bad_R.add(R)
                break
    for (U, K), i in Akey.items():
        tot += mass[i]
        if Rof[(U, K)] not in bad_R:
            exact_mass += mass[i]
    return amap, exact_mass / tot


if __name__ == "__main__":
    rng = random.Random(20260918)
    configs = [(24, 2, 2, 1, [0.5, 0.1, 0.02, 0.0]),
               (24, 2, 2, 2, [0.5, 0.1, 0.02, 0.0]),
               (30, 2, 3, 1, [0.0])]  # about 20 min in total on one core
    if len(sys.argv) > 1:
        configs = [configs[int(a)] for a in sys.argv[1:]]
    for n, D, k, l, betas in configs:
        EQ = regular_3lin(n, D, rng)
        for beta in betas:
            tuples, HUs, Aun, Akey, B, Wun, Wkey = build(EQ, k, l, beta)
            g0, _ = gap(Wun, len(Aun), len(B))
            g1, n1 = gap(Wkey, len(Akey), len(B))
            amap, ex = canonical(HUs, Akey, l, Wkey)
            g2, n2 = gap(Wkey, len(Akey), len(B), amap)
            print(f"n={n} D={D} k={k} l={l} beta={beta:<4} |tuples|={len(tuples)} "
                  f"|A|={len(Aun)} |B|={len(B)}  unfolded={g0:.5f}  "
                  f"within-U={g1:.5f} ({n1})  canonical={g2:.5f} ({n2})  "
                  f"exact-mass={ex:.3f}", flush=True)
    sys.exit(0)
