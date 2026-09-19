"""Column generation version of multilevel_lp.py for large assignment spaces.

Master LP (all observation keys k, all words s):
    min  sum_(s,k) (e+_(s,k) + e-_(s,k)) / 2
    s.t. sum_a p_a [obs_s(a) = k] - q_k - e+_(s,k) + e-_(s,k) = 0,   sum_a p_a = 1.
Its optimum is 0 iff a mixture makes law_s independent of s (then q is the law).
The value is min_p sum_s ||law_s - q||_1 / 2.
Pricing enumerates every assignment (vectorised) and adds those with negative
reduced cost; at termination (no negative reduced cost) the value is the exact
optimum over the full assignment space.
Usage: python3 colgen_lp.py m d L relax weights [maxiter]
"""
import sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

from multilevel_lp import piece_data, encode


def all_keys(m, d, L, relax, W, chunk=1 << 19):
    S, LV, pieces = piece_data(m, d)
    nl = len(LV)
    choices = [(0, 0)] + [(ell, w) for ell in range(1, L + 1) for w in W]
    nc = len(choices)
    cl = np.array([c[0] for c in choices]); cw = np.array([c[1] for c in choices])
    total = nc ** nl

    def chunks():
        for start in range(0, total, chunk):
            idx = np.arange(start, min(total, start + chunk), dtype=np.int64)
            digs = np.zeros((idx.size, nl), dtype=np.int64)
            t = idx.copy()
            for i in range(nl):
                digs[:, i] = t % nc
                t //= nc
            yield idx, encode(cl[digs], cw[digs], pieces, relax)
    return S, chunks


def run(m, d, L, relax, W, maxiter=400, verbose=True):
    S, chunks = all_keys(m, d, L, relax, W)
    ns = len(S)
    keyset = set()
    first = {}
    for idx, keys in chunks():
        for s in range(ns):
            keyset.update(np.unique(keys[:, s]).tolist())
        if not first:
            u, pos = np.unique(keys, axis=0, return_index=True)
            for r, p0 in zip(u[:2000], pos[:2000]):
                first[tuple(r)] = int(idx[p0])
    allk = np.array(sorted(keyset), dtype=np.int64)
    nk = len(allk)
    cols = dict(first)
    nrow = ns * nk + 1
    it = 0
    while True:
        it += 1
        sigs = list(cols)
        na = len(sigs)
        rows, cc, vals = [], [], []
        for j, sg in enumerate(sigs):
            for s in range(ns):
                k = int(np.searchsorted(allk, sg[s]))
                rows.append(s * nk + k); cc.append(j); vals.append(1.0)
            rows.append(ns * nk); cc.append(j); vals.append(1.0)
        for s in range(ns):
            for k in range(nk):
                r = s * nk + k
                rows += [r, r, r]
                cc += [na + k, na + nk + r, na + nk + ns * nk + r]
                vals += [-1.0, -1.0, 1.0]
        nv = na + nk + 2 * ns * nk
        A = coo_matrix((vals, (rows, cc)), shape=(nrow, nv)).tocsr()
        b = np.zeros(nrow); b[-1] = 1.0
        c = np.concatenate([np.zeros(na + nk), np.ones(2 * ns * nk) / 2])
        res = linprog(c, A_eq=A, b_eq=b, bounds=[(0, None)] * nv, method="highs")
        pi = res.eqlin.marginals
        P = pi[:-1].reshape(ns, nk); tau = pi[-1]
        best = []
        minrc = 0.0
        for idx, keys in chunks():
            ki = np.searchsorted(allk, keys)
            val = np.zeros(keys.shape[0])
            for s in range(ns):
                val += P[s, ki[:, s]]
            rc = -val - tau
            minrc = min(minrc, rc.min())
            sel = np.where(rc < -1e-9)[0]
            if sel.size:
                sel = sel[np.argsort(rc[sel])[:300]]
                for t in sel:
                    best.append((rc[t], tuple(keys[t]), int(idx[t])))
        if verbose:
            print(f"iter {it}: cols={na} obj={res.fun:.6f} min reduced cost={minrc:.2e}", flush=True)
        if not best or it >= maxiter:
            return res.fun, (not best), sigs, res.x[:na], allk
        best.sort()
        added = 0
        for rc, sg, a in best:
            if sg not in cols:
                cols[sg] = a
                added += 1
            if added >= 600:
                break
        if added == 0:
            return res.fun, True, sigs, res.x[:na], allk


if __name__ == "__main__":
    m, d, L, relax = map(int, sys.argv[1:5])
    W = tuple(int(x) for x in sys.argv[5].split(","))
    mi = int(sys.argv[6]) if len(sys.argv) > 6 else 400
    val, exact, sigs, x, allk = run(m, d, L, relax, W, mi)
    print(f"(m,d)=({m},{d}) L={L} W={W} R{relax}: optimum={'exact' if exact else 'upper bound'} {val:.6f}")
