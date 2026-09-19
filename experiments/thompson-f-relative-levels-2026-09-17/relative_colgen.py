"""Column generation with exact pricing for the relative-level LP of relative_level_lp.py.

Same model and observation (Obs_s: ordered partition of the middle positions by top level,
projective weight vector inside each block, level-gap ratios when there are >= 3 blocks),
vectorised so that {1..L}^n x W^n can be priced exhaustively in chunks.

Usage: python3 relative_colgen.py m d L w1,w2,... [obsmode]
  obsmode = full (default) | partition | top
Prints the exact minimum total violation  sum_(s>=1) || law Obs_s - law Obs_0 ||_1  of the
restricted-then-priced LP.  Pricing is exhaustive, so the final value is the exact LP optimum
over the whole configuration space.
"""
import itertools
import math
import sys

import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog

from relative_level_lp import setup

MODE = "full"


def encode(Lv, Wv, pieces):
    """Lv, Wv: (B, n) int arrays. pieces: list of leaf-index tuples. Returns (B, k) int code rows."""
    H = np.stack([Lv[:, list(P)].max(axis=1) for P in pieces], axis=1)
    C = np.stack([np.where(Lv[:, list(P)] == H[:, [j]], Wv[:, list(P)], 0).sum(axis=1)
                  for j, P in enumerate(pieces)], axis=1)
    B, k = H.shape
    srt = np.sort(H, axis=1)
    rank = np.zeros_like(H)
    for j in range(k):
        below = srt < H[:, [j]]
        first = np.ones_like(srt, dtype=bool)
        first[:, 1:] = srt[:, 1:] != srt[:, :-1]
        rank[:, j] = (below & first).sum(axis=1)
    if MODE == "top":
        return (rank == rank.max(axis=1, keepdims=True)).astype(np.int64)
    if MODE == "partition":
        return rank
    # projective weights inside blocks: divide by gcd over the block
    norm = np.zeros_like(C)
    for j in range(k):
        same = rank == rank[:, [j]]
        g = np.zeros(B, dtype=np.int64)
        for i in range(k):
            g = np.where(same[:, i], np.gcd(g, C[:, i]), g)
        norm[:, j] = C[:, j] // g
    nb = rank.max(axis=1) + 1
    gap = np.zeros((B, max(k - 1, 1)), dtype=np.int64)
    distinct = np.where(np.concatenate([np.ones((B, 1), bool), srt[:, 1:] != srt[:, :-1]], axis=1),
                        srt, -1)
    dv = -np.sort(-distinct, axis=1)  # distinct values descending, padded with -1
    for i in range(k - 1):
        gap[:, i] = np.where((dv[:, i + 1] >= 0) & (nb >= 3), dv[:, i] - dv[:, i + 1], 0)
    g = np.zeros(B, dtype=np.int64)
    for i in range(k - 1):
        g = np.gcd(g, gap[:, i])
    g = np.where(g == 0, 1, g)
    gap = gap // g[:, None]
    return np.concatenate([rank, norm, gap], axis=1)


def pack(rows):
    """Pack small non-negative code rows into one int64 key each (base 64)."""
    key = np.zeros(len(rows), dtype=np.int64)
    for i in range(rows.shape[1]):
        key = key * 64 + rows[:, i]
    return key


def all_configs(n, Lmax, W, chunk=1 << 18):
    wts = np.array(list(itertools.product(W, repeat=n)), dtype=np.int64)
    buf = []
    for lev in itertools.product(range(1, Lmax + 1), repeat=n):
        if min(lev) != 1:
            continue
        buf.append(lev)
        if len(buf) * len(wts) >= chunk:
            Lv = np.repeat(np.array(buf, dtype=np.int64), len(wts), axis=0)
            yield Lv, np.tile(wts, (len(buf), 1))
            buf = []
    if buf:
        Lv = np.repeat(np.array(buf, dtype=np.int64), len(wts), axis=0)
        yield Lv, np.tile(wts, (len(buf), 1))


def keys_of(Lv, Wv, L):
    return np.stack([pack(encode(Lv, Wv, P)) for P in L], axis=1)


def build_rows(K):
    """K: (N, ns) outcome keys. Row set: (s, outcome) for s >= 1."""
    ns = K.shape[1]
    rowkeys = {}
    ri, ci, vv = [], [], []
    for s in range(1, ns):
        diff = np.nonzero(K[:, s] != K[:, 0])[0]
        for col in diff:
            for key, sg in (((s, int(K[col, s])), 1.0), ((s, int(K[col, 0])), -1.0)):
                r = rowkeys.setdefault(key, len(rowkeys))
                ri.append(r), ci.append(col), vv.append(sg)
    return rowkeys, ri, ci, vv


def solve_master(K):
    N = len(K)
    rowkeys, ri, ci, vv = build_rows(K)
    R = len(rowkeys)
    A = sp.csr_matrix((vv, (ri, ci)), shape=(R, N))
    Aeq = sp.vstack([sp.hstack([A, -sp.eye(R), sp.eye(R)]),
                     sp.hstack([sp.csr_matrix(np.ones((1, N))), sp.csr_matrix((1, 2 * R))])]).tocsc()
    beq = np.zeros(R + 1)
    beq[-1] = 1
    cost = np.concatenate([np.zeros(N), np.ones(2 * R)])
    res = linprog(cost, A_eq=Aeq, b_eq=beq, bounds=(0, None), method="highs")
    return res, rowkeys


def run(m, d, Lmax, W, max_rounds=300, add_per_round=500, verbose=True, seed_cols=None):
    S, LV, L = setup(m, d)
    n, ns = len(LV), len(S)
    rng = np.random.default_rng(1)
    Lv = rng.integers(1, Lmax + 1, size=(300, n))
    Lv[:, 0] = 1
    Wv = rng.choice(np.array(W), size=(300, n))
    CL, CW = [Lv], [Wv]
    K = keys_of(Lv, Wv, L)
    for rnd in range(max_rounds):
        res, rowkeys = solve_master(K)
        R = len(rowkeys)
        y = res.eqlin.marginals
        yk, z = y[:R], y[R]
        # per word s: sorted arrays of (outcome key -> dual)
        lut = []
        for s in range(1, ns):
            ks = np.array([k[1] for k in rowkeys if k[0] == s], dtype=np.int64)
            vs = np.array([yk[r] for k, r in rowkeys.items() if k[0] == s])
            o = np.argsort(ks)
            lut.append((ks[o], vs[o]))

        def dual(s, keys):
            ks, vs = lut[s - 1]
            if len(ks) == 0:
                return np.zeros(len(keys))
            pos = np.clip(np.searchsorted(ks, keys), 0, len(ks) - 1)
            return np.where(ks[pos] == keys, vs[pos], 0.0)

        cand = []
        for Lv, Wv in all_configs(n, Lmax, W):
            Kc = keys_of(Lv, Wv, L)
            red = -z * np.ones(len(Lv))
            for s in range(1, ns):
                red -= np.where(Kc[:, s] == Kc[:, 0], 0.0, dual(s, Kc[:, s]) - dual(s, Kc[:, 0]))
            idx = np.argsort(red)[:add_per_round]
            idx = idx[red[idx] < -1e-9]
            if len(idx):
                cand.append((red[idx], Lv[idx], Wv[idx]))
        nimp = sum(len(c[0]) for c in cand)
        if verbose:
            print(f"round {rnd}: cols={len(K)} rows={R} value={res.fun:.6g} improving={nimp}", flush=True)
        if not cand:
            break
        red = np.concatenate([c[0] for c in cand])
        o = np.argsort(red)[:add_per_round]
        nl = np.concatenate([c[1] for c in cand])[o]
        nw = np.concatenate([c[2] for c in cand])[o]
        CL.append(nl), CW.append(nw)
        K = np.concatenate([K, keys_of(nl, nw, L)])
    return res.fun, np.concatenate(CL), np.concatenate(CW), res.x[:len(K)]


if __name__ == "__main__":
    m, d, Lmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    W = tuple(int(x) for x in sys.argv[4].split(",")) if len(sys.argv) > 4 else (1,)
    if len(sys.argv) > 5:
        MODE = sys.argv[5]
    val, CL, CW, p = run(m, d, Lmax, W)
    print(f"FINAL (m,d)=({m},{d}) L={Lmax} W={W} mode={MODE}: exact min violation = {val:.6g}")
    for k in np.argsort(-p)[:10]:
        if p[k] > 1e-9:
            print(f"  p={p[k]:.4f} levels={tuple(int(x) for x in CL[k])} weights={tuple(int(x) for x in CW[k])}")
