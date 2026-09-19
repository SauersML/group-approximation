#!/usr/bin/env python3
"""Limit density of context-constrained (SFT) forest window sets in Thompson's group F.

A family is (Sigma, A, Pi, C):
  Sigma  bulk alphabet (trees), A bulk adjacency (allowed consecutive bulk pairs),
  Pi     pointer alphabet, C a set of pointer contexts (S, P, T): S, T in Sigma, P in Pi.
Y_n = pointed forests (T_0..T_{m-1}; i) with n leaves such that every consecutive pair not
containing the pointer is A-allowed and (T_{i-1}, T_i, T_{i+1}) in C (window ends: see
finite-n checker).  As n -> infinity (A primitive), with M(R)[S,T] = A(S,T) R^|T| of spectral
radius 1, left/right Perron vectors l, r:
  vertex weight  w(S,P,T)            = l_S R^{|P|+|T|} r_T
  shift edge     (S,P,U)-(P,U,V)      = l_S R^{|P|+|U|+|V|} r_V  [A(S,P) A(U,V), P,U in Sigma]
  merge edge     (S,P,U)-(S,(P,U),V)  = l_S R^{|P|+|U|+|V|} r_V  [A(U,V), (P,U) in Pi]
  density = 2 c(E(C)) / w(C).
For fixed bulk the best C is a weighted densest-subgraph problem, solved exactly (up to float
scaling) by Dinkelbach + min cut.
"""
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import maximum_flow

_TREES = {1: [()]}


def trees(s):
    if s not in _TREES:
        _TREES[s] = [(L, R) for k in range(1, s) for L in trees(k) for R in trees(s - k)]
    return _TREES[s]


def size(T):
    return 1 if T == () else size(T[0]) + size(T[1])


def depth(T):
    return 0 if T == () else 1 + max(depth(T[0]), depth(T[1]))


def all_trees(N):
    return [T for s in range(1, N + 1) for T in trees(s)]


def perron(Sigma, A):
    """R with rho(M(R)) = 1, and Perron vectors l (lM=l), r (Mr=r), normalised l.r = 1."""
    sz = np.array([size(T) for T in Sigma], dtype=float)
    A = np.asarray(A, dtype=float)

    def rho(R):
        M = A * (R ** sz)[None, :]
        return max(abs(np.linalg.eigvals(M)))
    lo, hi = 1e-9, 1.0
    if rho(hi) < 1:
        raise ValueError('rho(M(1)) < 1: finite language')
    for _ in range(100):
        mid = (lo + hi) / 2
        if rho(mid) < 1:
            lo = mid
        else:
            hi = mid
    R = hi
    M = A * (R ** sz)[None, :]
    ev, V = np.linalg.eig(M)
    k = np.argmax(ev.real)
    r = np.abs(V[:, k].real)
    ev, V = np.linalg.eig(M.T)
    k = np.argmax(ev.real)
    l = np.abs(V[:, k].real)
    l = l / (l @ r)
    return R, l, r


def build(Sigma, A, Pi, R, l, r):
    """vertices (S,P,T) as index triples, weights, and edges (u, v, c)."""
    sidx = {T: j for j, T in enumerate(Sigma)}
    pidx = {T: j for j, T in enumerate(Pi)}
    nS, nP = len(Sigma), len(Pi)
    szS = np.array([size(T) for T in Sigma])
    szP = np.array([size(T) for T in Pi])
    A = np.asarray(A, dtype=bool)

    def vid(s, p, t):
        return (s * nP + p) * nS + t
    nv = nS * nP * nS
    w = np.zeros(nv)
    for s in range(nS):
        for p in range(nP):
            for t in range(nS):
                w[vid(s, p, t)] = l[s] * R ** (szP[p] + szS[t]) * r[t]
    eu, ev, ec, et = [], [], [], []
    # shift edges
    both = [(j, pidx[T]) for j, T in enumerate(Sigma) if T in pidx]
    for s in range(nS):
        for (ps, pp) in both:
            if not A[s, ps]:
                continue
            for (us, up) in both:
                for v in range(nS):
                    if not A[us, v]:
                        continue
                    eu.append(vid(s, pp, us))
                    ev.append(vid(ps, up, v))
                    ec.append(l[s] * R ** (szS[ps] + szS[us] + szS[v]) * r[v])
                    et.append(0)
    # merge edges
    for p, P in enumerate(Pi):
        for us, U in enumerate(Sigma):
            M = (P, U)
            if M not in pidx:
                continue
            m = pidx[M]
            for s in range(nS):
                for v in range(nS):
                    if not A[us, v]:
                        continue
                    eu.append(vid(s, p, us))
                    ev.append(vid(s, m, v))
                    ec.append(l[s] * R ** (szP[p] + szS[us] + szS[v]) * r[v])
                    et.append(1)
    return w, np.array(eu), np.array(ev), np.array(ec), np.array(et)


def densest(w, eu, ev, ec, iters=40, scale=None, verbose=False):
    """max_C 2 c(E(C)) / w(C) by Dinkelbach with integer min cuts.  Returns (density, mask)."""
    nv = len(w)
    keep = w > 0
    mask = keep.copy()

    def dens(mask):
        inside = mask[eu] & mask[ev]
        return 2 * ec[inside].sum() / w[mask].sum()
    g = dens(mask)
    if scale is None:
        scale = 2e8 / max(ec.sum(), w.sum())
    for it in range(iters):
        # maximise sum_{e in C} 2 c_e - g w(C):  cut = sum_{v in C}(g w_v - d_v)^+... (see docstring)
        d = np.zeros(nv)
        np.add.at(d, eu, ec)
        np.add.at(d, ev, ec)
        b = d - g * w  # vertex benefit (times 1); edge crossing penalty c_e
        src, dst = nv, nv + 1
        cap_s = np.maximum(0, b)
        cap_t = np.maximum(0, -b)
        rows = np.concatenate([eu, ev, np.full(nv, src), np.arange(nv)])
        cols = np.concatenate([ev, eu, np.arange(nv), np.full(nv, dst)])
        caps = np.concatenate([ec, ec, cap_s, cap_t])
        capi = np.round(caps * scale).astype(np.int64)
        good = capi > 0
        G = csr_matrix((capi[good].astype(np.int32), (rows[good], cols[good])), shape=(nv + 2, nv + 2))
        res = maximum_flow(G, src, dst)
        F = res.flow
        # residual reachability from src
        resid = csr_matrix(G.astype(np.int64) - F.astype(np.int64))  # flow is antisymmetric
        resid.data[resid.data < 0] = 0
        resid.eliminate_zeros()
        from scipy.sparse.csgraph import breadth_first_order
        order = breadth_first_order(resid, src, directed=True, return_predecessors=False)
        newmask = np.zeros(nv, dtype=bool)
        order = order[order < nv]
        newmask[order] = True
        newmask &= keep
        if not newmask.any():
            break
        g2 = dens(newmask)
        if verbose:
            print('  it %d  density %.6f  |C|=%d' % (it, g2, newmask.sum()), flush=True)
        if g2 <= g + 1e-10:
            if g2 > g:
                g, mask = g2, newmask
            break
        g, mask = g2, newmask
    return g, mask


def family_density(Sigma, A, Pi, verbose=False):
    R, l, r = perron(Sigma, A)
    w, eu, ev, ec, et = build(Sigma, A, Pi, R, l, r)
    full = 2 * ec.sum() / w.sum()
    g, mask = densest(w, eu, ev, ec, verbose=verbose)
    return R, full, g, mask


if __name__ == '__main__':
    import sys
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    Np = int(sys.argv[2]) if len(sys.argv) > 2 else N + 1
    Sigma = all_trees(N)
    Pi = all_trees(Np)
    A = np.ones((len(Sigma), len(Sigma)))
    R, full, g, mask = family_density(Sigma, A, Pi, verbose=True)
    print('N=%d Np=%d  R=%.6f  all-contexts density=%.6f  best-context density=%.6f'
          % (N, Np, R, full, g))
