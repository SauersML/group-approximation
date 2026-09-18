#!/usr/bin/env python3
"""Spectral gap of small DKKMS 2-to-1 hosts as a function of the smoothing beta.

The constraint graph of an orientation lift is the constraint graph of the
2-to-1 game (orientation-lifts-sandwich-2to1-game-values). This script builds
the DKKMS edge process (TR16-198 Sec 4.2, as quoted verbatim in
dkkms-2to1-instances-satisfy-selector-decoding-hypotheses) on a small regular
3LIN instance and reports lambda_2 = 1 - sigma_2 of the normalized bipartite
host, unfolded and folded.

Instance: the 12 lines of the affine plane AG(2,3) on 9 variables (each variable
in 4 equations); legitimate k-tuples are sets of k pairwise disjoint lines.
Edge process: U uniform; V_i = e_i w.p. 1-beta, else a uniform variable of e_i;
L' uniform in Gr(X_V, l-1); L uniform among l-spaces of X_U containing L';
restricted to L meet H_U = 0 and renormalised.
Foldings: within-U (blocks (U, L + H_U); finest, so a lower bound for any
Lemma 4.1 folding, since merging A-vertices can only raise lambda_2) and
canonical (fibres of the least-support admissible representative R; one valid
Lemma 4.1-form partition). On this dense 9-variable instance k-tuples overlap
heavily; dkkms_folded_gap_large.py repeats the measurement on sparse systems.
At k = 2 the canonical folded gap stays near 0.09 as beta -> 0 while the
unfolded gap vanishes.
"""
import itertools
import sys
from collections import defaultdict

import numpy as np

NV = 9
POINTS = [(x, y) for x in range(3) for y in range(3)]
PID = {p: i for i, p in enumerate(POINTS)}


def ag23_lines():
    lines = set()
    for p, q in itertools.combinations(POINTS, 2):
        d = ((q[0] - p[0]) % 3, (q[1] - p[1]) % 3)
        pts = frozenset(PID[((p[0] + t * d[0]) % 3, (p[1] + t * d[1]) % 3)]
                        for t in range(3))
        lines.add(pts)
    return sorted(tuple(sorted(l)) for l in lines)


EQ = ag23_lines()
assert len(EQ) == 12


def span(vecs):
    s = {0}
    for v in vecs:
        s |= {x ^ v for x in s}
    return frozenset(s)


def subspaces_of(support_mask, dim):
    """All dim-subspaces of the coordinate space on support_mask."""
    coords = [i for i in range(NV) if support_mask >> i & 1]
    vecs = [sum(1 << coords[j] for j in range(len(coords)) if m >> j & 1)
            for m in range(1, 1 << len(coords))]
    out = set()
    if dim == 0:
        return [frozenset([0])]
    for basis in itertools.combinations(vecs, dim):
        s = span(basis)
        if len(s) == 1 << dim:
            out.add(s)
    return list(out)


def mask(vars_):
    return sum(1 << v for v in vars_)


def build(k, l, beta):
    tuples = [c for c in itertools.combinations(range(12), k)
              if len(set().union(*[set(EQ[i]) for i in c])) == 3 * k]
    A, B = {}, {}
    W = defaultdict(float)
    sub_cache = {}

    def subs(m, d):
        if (m, d) not in sub_cache:
            sub_cache[(m, d)] = subspaces_of(m, d)
        return sub_cache[(m, d)]

    for U in tuples:
        XU = mask(v for i in U for v in EQ[i])
        HU = span([mask(EQ[i]) for i in U])
        up = defaultdict(list)  # (l-1)-space -> l-spaces of X_U containing it
        for L in subs(XU, l):
            vs = sorted(L - {0})
            for basis in itertools.combinations(vs, l - 1):
                s = span(basis)
                if len(s) == 1 << (l - 1):
                    up[s].append(L)
        up = {s: list(set(v)) for s, v in up.items()}
        # V choices: per coordinate, the equation or one of its 3 variables
        opts = [[(('e', i), 1 - beta)] + [(('x', v), beta / 3) for v in EQ[i]]
                for i in U]
        for choice in itertools.product(*opts):
            pV = np.prod([c[1] for c in choice])
            if pV == 0:
                continue
            V = tuple(sorted(c[0] for c in choice))
            XV = mask(v for t, a in V for v in (EQ[a] if t == 'e' else [a]))
            Lps = subs(XV, l - 1)
            for Lp in Lps:
                ups = up[Lp] if l > 1 else subs(XU, l)
                good = [L for L in ups if len(L & HU) == 1]
                for L in good:
                    w = pV / len(Lps) / len(ups)
                    a = A.setdefault((U, L), len(A))
                    b = B.setdefault((V, Lp), len(B))
                    W[(a, b)] += w
    return tuples, A, B, W


def gap(nA, nB, W, amap=None):
    if amap is not None:
        W2 = defaultdict(float)
        for (a, b), w in W.items():
            W2[(amap[a], b)] += w
        W, nA = W2, max(amap) + 1
    M = np.zeros((nA, nB))
    for (a, b), w in W.items():
        M[a, b] += w
    r, c = M.sum(1), M.sum(0)
    keepA, keepB = r > 0, c > 0
    M = M[keepA][:, keepB]
    r, c = r[keepA], c[keepB]
    N = M / np.sqrt(r)[:, None] / np.sqrt(c)[None, :]
    s = np.linalg.svd(N, compute_uv=False)
    return 1 - s[1], M.shape


def fold_within(A):
    """Finest folding: merge (U,L),(U,L2) with L + H_U = L2 + H_U (same U only).
    Every Lemma 4.1 class is a union of these blocks, and merging A-vertices can
    only raise lambda_2, so this is a LOWER bound for any folded host."""
    HU, roots, amap = {}, {}, [0] * len(A)
    for (U, L), i in A.items():
        if U not in HU:
            HU[U] = span([mask(EQ[j]) for j in U])
        amap[i] = roots.setdefault((U, span(list(L | HU[U]))), len(roots))
    return amap


def fold_canon(A, l):
    """One legitimate Lemma 4.1 partition: (U, K = L + H_U) is assigned the
    admissible representative R (dim l, R inside K, R meet H_U = 0) of least
    support, ties broken lexicographically; blocks are the fibres of U,K -> R.
    Each block lies in {(U,L): L + H_U = R + H_U}, so it is a valid folding.
    Cross-U merging happens whenever two tuples pick the same R."""
    HU, roots, amap = {}, {}, [0] * len(A)
    for (U, L), i in A.items():
        if U not in HU:
            HU[U] = span([mask(EQ[j]) for j in U])
        K = span(list(L | HU[U]))
        best = None
        for b in itertools.combinations(sorted(K - {0}), l):
            R = span(b)
            if len(R) != 1 << l or len(R & HU[U]) != 1:
                continue
            sup = 0
            for v in R:
                sup |= v
            key = (bin(sup).count("1"), tuple(sorted(R)))
            if best is None or key < best:
                best = key
        amap[i] = roots.setdefault(best[1], len(roots))
    return amap


if __name__ == "__main__":
    for k, l in [(1, 2), (2, 2)]:
        for beta in [0.5, 0.1, 0.02]:
            tuples, A, B, W = build(k, l, beta)
            g0, s0 = gap(len(A), len(B), W)
            g1, s1 = gap(len(A), len(B), W, fold_within(A))
            g2, s2 = gap(len(A), len(B), W, fold_canon(A, l))
            print(f"k={k} l={l} beta={beta:<4} unfolded={g0:.5f} {s0} "
                  f"within-U={g1:.5f} {s1} canonical={g2:.5f} {s2} "
                  f"canonical/beta={g2 / beta:.3f}", flush=True)
    sys.exit(0)
