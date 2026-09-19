"""Symmetry setup for the Had_k -> Max-2Lin(2) gadget minimax at general k.

Vertices of Q = {-1,1}^K (K = 2^k) are K-bit masks, bit i set iff x_i = -1.
Coordinates i in F_2^k.  Primaries chi_a, mask m_a = {i : a.i odd}.
Group: affine maps i -> M i + v of F_2^k acting on coordinates, and x -> -x.
Orbits are computed from generators only (transvections, translations,
negation) with connected components, so k = 4 (65536 vertices, 524288 edges)
is cheap.

Edges are stored as (x, j) with bit j of x clear; index x*K + j is not used,
instead a dense list.  Folded vertex rep: x with top bit clear.
"""
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components


def coord_perms(k):
    K = 1 << k
    gens = []
    idx = np.arange(K)
    # translations by e_c
    for c in range(k):
        gens.append(idx ^ (1 << c))
    # transvections e_r <- e_r + e_c : i -> i with bit r xor= bit c
    for r in range(k):
        for c in range(k):
            if r != c:
                gens.append(idx ^ (((idx >> c) & 1) << r))
    return gens


def act_masks(perm, masks, K):
    """image of bit masks under coordinate permutation perm (bit i -> bit perm[i])."""
    out = np.zeros_like(masks)
    for i in range(K):
        out |= ((masks >> i) & 1) << int(perm[i])
    return out


def setup(k, first=0):
    K = 1 << k
    N = 1 << K
    full = N - 1
    dt = np.int64
    prim = np.array([sum(1 << i for i in range(K) if bin(a & i).count("1") % 2)
                     for a in range(first, K)], dtype=dt)
    P = len(prim)
    pidx = {int(m): a for a, m in enumerate(prim)}
    gens = coord_perms(k)
    # edges: (x, j) with bit j of x clear
    xs = np.arange(N, dtype=dt)
    ex, ej = [], []
    for j in range(K):
        sel = xs[((xs >> j) & 1) == 0]
        ex.append(sel); ej.append(np.full(len(sel), j, dtype=dt))
    ex = np.concatenate(ex); ej = np.concatenate(ej)
    E = len(ex)
    # index lookup: edge id of (x, j) with x_j clear: pos[j][x >> ... ] use dict via array
    # position of x among those with bit j clear: compress by removing bit j
    def eid(x, j):
        lo = x & ((1 << j) - 1)
        hi = x >> (j + 1)
        return j * (N >> 1) + ((hi << j) | lo)
    assert np.all(eid(ex, ej) == np.arange(E))
    rows, cols = [], []
    for g in gens:
        gx = act_masks(g, ex, K)
        gj = np.asarray(g)[ej]
        gy = gx ^ (np.int64(1) << gj)
        base = np.where(((gx >> gj) & 1) == 0, gx, gy)
        rows.append(np.arange(E)); cols.append(eid(base, gj))
    # negation: (x,j) -> (~x, j) with bit j of ~x set, so base is ~x ^ bit j
    nx = (ex ^ full) ^ (np.int64(1) << ej)
    rows.append(np.arange(E)); cols.append(eid(nx, ej))
    r = np.concatenate(rows); c = np.concatenate(cols)
    G = coo_matrix((np.ones(len(r), dtype=np.int8), (r, c)), shape=(E, E))
    norb, orb = connected_components(G, directed=True, connection="weak")
    osize = np.bincount(orb, minlength=norb)
    # patterns xi in {0,1}^P, bit a set iff xi_a = -1
    npat = 1 << P
    pats = np.arange(npat, dtype=dt)
    prow, pcol = [], []
    for g in gens + ["neg"]:
        out = np.zeros(npat, dtype=dt)
        for a, m in enumerate(prim):
            if isinstance(g, str):
                gm = int(m) ^ full
            else:
                gm = int(act_masks(g, np.array([m], dtype=dt), K)[0])
            bit = (pats >> a) & 1
            if gm in pidx:
                out |= bit << pidx[gm]
            else:
                out |= (1 - bit) << pidx[gm ^ full]
        prow.append(pats); pcol.append(out)
    r = np.concatenate(prow); c = np.concatenate(pcol)
    Gp = coo_matrix((np.ones(len(r), dtype=np.int8), (r, c)), shape=(npat, npat))
    nq, porb = connected_components(Gp, directed=True, connection="weak")
    psize = np.bincount(porb, minlength=nq)
    reps = np.array([np.flatnonzero(porb == q)[0] for q in range(nq)])
    return dict(k=k, K=K, N=N, full=full, prim=prim, ex=ex, ej=ej, E=E,
                orb=orb, norb=norb, osize=osize, porb=porb, reps=reps,
                psize=psize, npat=npat, eid=eid)


if __name__ == "__main__":
    import sys, time
    for k in [int(a) for a in sys.argv[1:]] or [3]:
        t = time.time()
        S = setup(k)
        print(k, "edges", S["E"], "edge orbits", S["norb"], "pattern orbits",
              len(S["reps"]), "time %.1f" % (time.time() - t))
