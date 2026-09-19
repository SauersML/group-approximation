"""Exact pricing oracle: min over folded f with f(chi_a) = xi_a of sum_e w_e cut_e(f).

Min-2Lin(2)-deletion on the 2^(K-1) folded vertex classes, solved as a MILP
with HiGHS.  Only edges of positive weight enter the model.  Returns the
optimum, the MIP dual bound, and the cut indicator of the returned f on all E
edges (so it can be orbit-averaged into a column).
"""
import numpy as np
import highspy
from scipy.sparse import csc_matrix


def canon_edges(S):
    """canonical folded edge id for every edge: min(e, neg(e))."""
    if "cedge" in S:
        return S["cedge"]
    ex, ej, full, eid = S["ex"], S["ej"], S["full"], S["eid"]
    nx = (ex ^ full) ^ (np.int64(1) << ej)
    ne = eid(nx, ej)
    S["cedge"] = np.minimum(np.arange(S["E"]), ne)
    return S["cedge"]


def price(S, w, xi, time_limit=600.0, gap=1e-9, verbose=False, start=None):
    K, N, full, ex, ej = S["K"], S["N"], S["full"], S["ex"], S["ej"]
    half = N >> 1
    ce = canon_edges(S)
    wc = np.bincount(ce, weights=w, minlength=S["E"])
    live = np.flatnonzero(wc > 1e-15)
    x = ex[live]; y = x ^ (np.int64(1) << ej[live])
    top = np.int64(1) << (K - 1)
    sx = (x & top) != 0; sy = (y & top) != 0
    rx = np.where(sx, x ^ full, x); ry = np.where(sy, y ^ full, y)
    par = sx ^ sy
    nb = half; ne = len(live)
    # variables: b_0..b_{nb-1} binary, c_0..c_{ne-1} in [0,1]
    # par 0: c - b_x + b_y >= 0, c + b_x - b_y >= 0
    # par 1: c + b_x + b_y >= 1, c - b_x - b_y >= -1
    e = np.arange(ne)
    rows = np.concatenate([2 * e, 2 * e, 2 * e, 2 * e + 1, 2 * e + 1, 2 * e + 1])
    cols = np.concatenate([nb + e, rx, ry, nb + e, rx, ry])
    sgn = np.where(par, 1.0, -1.0)
    vals = np.concatenate([np.ones(ne), sgn, -sgn, np.ones(ne), -sgn, sgn])
    # fix: par0 row1: -b_x + b_y ; row2: +b_x - b_y.  par1 row1: +b_x + b_y ; row2: -b_x - b_y
    v1x = np.where(par, 1.0, -1.0); v1y = np.where(par, 1.0, 1.0)
    v2x = np.where(par, -1.0, 1.0); v2y = np.where(par, -1.0, -1.0)
    vals = np.concatenate([np.ones(ne), v1x, v1y, np.ones(ne), v2x, v2y])
    lo = np.empty(2 * ne)
    lo[0::2] = np.where(par, 1.0, 0.0)
    lo[1::2] = np.where(par, -1.0, 0.0)
    A = csc_matrix((vals, (rows, cols)), shape=(2 * ne, nb + ne))
    A.sum_duplicates()
    lb = np.zeros(nb + ne); ub = np.ones(nb + ne)
    for a, m in enumerate(S["prim"]):
        want = (int(xi) >> a) & 1              # 1 iff f(chi_a) = -1
        m = int(m)
        s = 1 if (m & int(top)) else 0
        r = m ^ full if s else m
        lb[r] = ub[r] = want ^ s
    cost = np.r_[np.zeros(nb), wc[live]]
    h = highspy.Highs()
    h.setOptionValue("output_flag", verbose)
    h.setOptionValue("time_limit", float(time_limit))
    h.setOptionValue("mip_rel_gap", gap)
    h.setOptionValue("threads", 1)
    lp = highspy.HighsLp()
    lp.num_col_ = nb + ne
    lp.num_row_ = 2 * ne
    lp.col_cost_ = cost
    lp.col_lower_ = lb
    lp.col_upper_ = ub
    lp.row_lower_ = lo
    lp.row_upper_ = np.full(2 * ne, highspy.kHighsInf)
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = A.indptr
    lp.a_matrix_.index_ = A.indices
    lp.a_matrix_.value_ = A.data
    lp.integrality_ = [highspy.HighsVarType.kInteger] * nb + [highspy.HighsVarType.kContinuous] * ne
    h.passModel(lp)
    if start is not None:
        sol = highspy.HighsSolution()
        sol.col_value = list(np.r_[start, np.zeros(ne)])
        h.setSolution(sol)
    h.run()
    info = h.getInfo()
    b = np.round(np.array(h.getSolution().col_value[:nb])).astype(np.int64)
    # cut indicator on all edges
    X = ex; Y = ex ^ (np.int64(1) << ej)
    SX = (X & top) != 0; SY = (Y & top) != 0
    RX = np.where(SX, X ^ full, X); RY = np.where(SY, Y ^ full, Y)
    fX = b[RX] ^ SX; fY = b[RY] ^ SY
    cut = (fX != fY).astype(float)
    return float(cut @ w), float(info.mip_dual_bound), cut, b
