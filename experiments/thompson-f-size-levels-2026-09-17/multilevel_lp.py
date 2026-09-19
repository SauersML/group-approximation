"""Random MULTI-LEVEL paddings for the size observation: exact LP.

Setting (research/thompson-f-tree-size-observations-have-zero-defect.md, class P
generalised).  m + 1 roots with complete depth-d tops, absorbing atoms at the two
extreme depth-d leaves, and at every other depth-d leaf v a random LEVEL
a(v) in {0, 1, ..., L} (0 = bare leaf).  Levels are infinitely separated scales
(lambda_1 << lambda_2 << ...), each mixed log-uniformly on its own range.

For a word s the middle pieces p_1..p_(w-1) (w = m + d) have top level
ell_j = max a(v) over v below p_j and count c_j = #{v below p_j : a(v) = ell_j}.

Relaxations of the observation of the middle pieces (weakest first):
  R0 : the level vector (ell_1, ..., ell_(w-1)), together with the depth of p_j
       whenever ell_j = 0 (a bare piece is an exact small tree, so its shape,
       hence its depth, is visible; without this the all-bare padding would be
       a trivial solution);
  R1 : R0 + for each level ell >= 1 the projective class of (c_j : ell_j = ell).
Any shadow law in the multi-level class makes the law of the TRUE observation
(sizes and depths) nearly s-independent, which forces the law of each R_i to be
exactly s-independent (R_i is a limit functional of the observation, see the
claim file).  So infeasibility of R0 (resp. R1) kills the whole class, whatever the
weights, counts or noise.

We minimise sum_s TV(law_s, law_(s0)) over mixtures of assignments by LP, after
merging assignments with identical signature (obs_s)_s.
Usage: python3 multilevel_lp.py m d L relax [weights, e.g. 1,2]
"""
import itertools
import sys
from collections import defaultdict
from fractions import Fraction
from math import gcd
import os

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "thompson-f-size-observation-2026-09-17"))
from level_search import monomial_set  # noqa: E402
from equal_middle_lp import antichain, leaves  # noqa: E402


def piece_data(m, d):
    S = monomial_set(m, d)
    LV = leaves(m, d)
    pieces = []
    for w in S:
        pcs = antichain(m, w)[1:-1]
        pieces.append([([i for i, (b, r) in enumerate(LV) if b == a and r.startswith(q)], len(q))
                       for (a, q) in pcs])
    return S, LV, pieces


def encode(asg_lev, asg_w, pieces, relax):
    """Vectorised observation keys.  asg_lev, asg_w: (N, n_leaves) int arrays.
    Returns (N, n_words) int64 keys; weight 0 is used on bare leaves."""
    N = asg_lev.shape[0]
    keys = np.zeros((N, len(pieces)), dtype=np.int64)
    for s, ps in enumerate(pieces):
        lev, ws, hs = [], [], []
        for ids, h in ps:
            if ids:
                top = asg_lev[:, ids].max(axis=1)
                wsum = ((asg_lev[:, ids] == top[:, None]) * asg_w[:, ids]).sum(axis=1)
            else:
                top = np.zeros(N, dtype=np.int64)
                wsum = np.zeros(N, dtype=np.int64)
            wsum = np.where(top == 0, 0, wsum)
            lev.append(top); ws.append(wsum); hs.append(h)
        lev = np.stack(lev, 1); ws = np.stack(ws, 1)
        if relax >= 1:
            g = np.zeros_like(ws)
            for ell in range(1, lev.max() + 1 if lev.size else 1):
                msk = lev == ell
                gl = np.gcd.reduce(np.where(msk, ws, 0), axis=1)
                g = np.where(msk, gl[:, None], g)
            val = np.where(lev == 0, np.array(hs)[None, :], ws // np.maximum(g, 1))
        else:
            val = np.where(lev == 0, np.array(hs)[None, :], 0)
        k = np.zeros(N, dtype=np.int64)
        for j in range(lev.shape[1]):
            k = k * 16 + lev[:, j]
            k = k * 256 + val[:, j]
        keys[:, s] = k
    return keys


def solve(m, d, L, relax, W=(1,)):
    S, LV, pieces = piece_data(m, d)
    ns, nl = len(S), len(LV)
    choices = [(0, 0)] + [(ell, w) for ell in range(1, L + 1) for w in W]
    nc = len(choices)
    cl = np.array([c[0] for c in choices]); cw = np.array([c[1] for c in choices])
    total = nc ** nl
    sigs = {}
    chunk = 1 << 20
    for start in range(0, total, chunk):
        idx = np.arange(start, min(total, start + chunk), dtype=np.int64)
        digs = np.zeros((idx.size, nl), dtype=np.int64)
        t = idx.copy()
        for i in range(nl):
            digs[:, i] = t % nc
            t //= nc
        keys = encode(cl[digs], cw[digs], pieces, relax)
        u = np.unique(keys, axis=0)
        for row in map(tuple, u):
            sigs[row] = 1
    sigs = list(sigs)
    allk = sorted({o for sg in sigs for o in sg})
    kid = {k: i for i, k in enumerate(allk)}
    na, nk = len(sigs), len(allk)
    nu = (ns - 1) * nk
    rows, cols, vals = [], [], []
    for s in range(1, ns):
        for k in range(nk):
            base = 2 * ((s - 1) * nk + k)
            rows += [base, base + 1]; cols += [na + (s - 1) * nk + k] * 2; vals += [-1.0, -1.0]
        for j, sg in enumerate(sigs):
            ks, k0 = kid[sg[s]], kid[sg[0]]
            if ks == k0:
                continue
            for k, sgn in ((ks, 1.0), (k0, -1.0)):
                base = 2 * ((s - 1) * nk + k)
                rows += [base, base + 1]; cols += [j, j]; vals += [sgn, -sgn]
    A = coo_matrix((vals, (rows, cols)), shape=(2 * nu, na + nu)).tocsr()
    A_eq = np.zeros((1, na + nu))
    A_eq[0, :na] = 1.0
    c = np.concatenate([np.zeros(na), np.ones(nu) / 2])
    res = linprog(c, A_ub=A, b_ub=np.zeros(2 * nu), A_eq=A_eq, b_eq=[1.0],
                  bounds=[(0, None)] * (na + nu), method="highs")
    return res, sigs, allk, S


if __name__ == "__main__":
    m, d, L, relax = map(int, sys.argv[1:5])
    W = tuple(int(x) for x in sys.argv[5].split(",")) if len(sys.argv) > 5 else (1,)
    res, sigs, keys, S = solve(m, d, L, relax, W)
    print(f"(m,d)=({m},{d}) L={L} W={W} R{relax}: signatures={len(sigs)} obs={len(keys)} "
          f"min total violation={res.fun:.6f}")
    if res.fun < 1e-9:
        x = res.x[:len(sigs)]
        for j in np.argsort(-x)[:12]:
            if x[j] > 1e-9:
                print(f"  p={x[j]:.4f}  s0-obs={sigs[j][0]}")
