"""Pricing oracles on the full cube Q = {-1,1}^K.

unfolded_price: exact min over f : Q -> {-1,1} (NOT required folded) with
  f(chi_a) = xi_a and f(-chi_a) = -xi_a of sum_e w_e [f cuts e].  This is an
  s-t min cut, solved by max flow on integer capacities.  Since every folded
  f is feasible, it is a lower bound on the folded pricing value.

fold_repair: from an unfolded min cut, build a folded f (f(-x) = -f(x)) and
  improve it by greedy antipodal-pair flips.  Gives a feasible folded column,
  hence an upper bound on the folded pricing value.
"""
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import maximum_flow, breadth_first_order

BIG = 1 << 40


def edge_ends(S):
    if "ey" not in S:
        S["ey"] = S["ex"] ^ (np.int64(1) << S["ej"])
    return S["ex"], S["ey"]


def pins(S, xi):
    """list of (vertex, value) with value 1 for +1."""
    full = S["full"]
    out = []
    for a, m in enumerate(S["prim"]):
        v = 0 if (int(xi) >> a) & 1 else 1      # f(chi_a) = +1 iff bit clear
        out.append((int(m), v)); out.append((int(m) ^ full, 1 - v))
    return out


_LIB = None


def _lib():
    """compile hadk_flow.c (int64 Dinic) once into a temp dir; scipy's maximum_flow is int32."""
    global _LIB
    if _LIB is None:
        import ctypes, os, subprocess, tempfile
        src = os.path.join(os.path.dirname(os.path.abspath(__file__)), "hadk_flow.c")
        out = os.path.join(os.environ.get("HADK_BUILD", tempfile.gettempdir()), "hadk_flow.so")
        if not os.path.exists(out) or os.path.getmtime(out) < os.path.getmtime(src):
            subprocess.check_call(["gcc", "-O2", "-shared", "-fPIC", "-o", out, src])
        L = ctypes.CDLL(out)
        P = np.ctypeslib.ndpointer
        L.mincut.restype = ctypes.c_longlong
        L.mincut.argtypes = [ctypes.c_int, ctypes.c_int, P(np.int32), P(np.int32), P(np.int64),
                             ctypes.c_int, ctypes.c_int, P(np.uint8)]
        _LIB = L
    return _LIB


def unfolded_price(S, cap, xi):
    """cap: integer capacity per edge (int64 array of length E).  Exact s-t min cut."""
    N = S["N"]
    ex, ey = edge_ends(S)
    live = cap > 0
    src, snk = N, N + 1
    pu, pv_, pd = [], [], []
    for v, val in pins(S, xi):
        pu.append(src if val == 1 else v); pv_.append(v if val == 1 else snk); pd.append(BIG)
    u = np.ascontiguousarray(np.r_[ex[live], pu], dtype=np.int32)
    v = np.ascontiguousarray(np.r_[ey[live], pv_], dtype=np.int32)
    c = np.ascontiguousarray(np.r_[cap[live], pd], dtype=np.int64)
    assert int(cap.sum()) < BIG
    side = np.zeros(N + 2, dtype=np.uint8)
    flow = _lib().mincut(N + 2, len(u), u, v, c, src, snk, side)
    f = side[:N].astype(bool)          # True = +1
    cut = (f[ex] != f[ey])
    assert flow < BIG and int(cap[cut].sum()) == flow
    return int(flow), cut, f


def cut_value(S, w, f):
    ex, ey = edge_ends(S)
    return float(((f[ex] != f[ey]) * w).sum())


def fold_repair(S, w, f0, xi, sweeps=4):
    """folded f from f0: on each antipodal pair keep f0(x) for the rep x with top bit clear,
    then greedy pair flips while they lower the weighted cut."""
    N, K, full = S["N"], S["K"], S["full"]
    ex, ey = edge_ends(S)
    half = N >> 1
    xs = np.arange(N, dtype=np.int64)
    rep = np.where(xs < half, xs, xs ^ full)
    sgn = xs >= half
    b = f0[:half].copy()                # value at rep (True = +1)
    fixed = np.zeros(half, dtype=bool)
    for v, val in pins(S, xi):
        r = v if v < half else v ^ full
        want = bool(val) if v < half else not bool(val)
        b[r] = want; fixed[r] = True
    # adjacency weights per rep for fast delta: build sparse incidence
    def full_f(b):
        return np.where(sgn, ~b[rep], b[rep])
    # delta of flipping rep r: all edges touching r or its antipode
    re_x, re_y = rep[ex], rep[ey]
    for _ in range(sweeps):
        f = full_f(b)
        c = (f[ex] != f[ey])
        # contribution change if a rep is flipped: edges with exactly one end in the pair class
        one = re_x != re_y
        gain = np.zeros(half)
        sgnw = np.where(c, w, -w) * one          # flipping removes cut (+w) or adds (-w)
        np.add.at(gain, re_x, sgnw)
        np.add.at(gain, re_y, sgnw)
        gain[fixed] = 0
        cand = np.flatnonzero(gain > 1e-15)
        if len(cand) == 0:
            break
        # flip an independent-ish subset greedily: take best, sequentially checked
        order = cand[np.argsort(-gain[cand])]
        improved = False
        for r in order[:2000]:
            f = full_f(b)
            before = cut_value(S, w, f)
            b[r] = ~b[r]
            after = cut_value(S, w, full_f(b))
            if after < before - 1e-15:
                improved = True
            else:
                b[r] = ~b[r]
        if not improved:
            break
    f = full_f(b)
    return f
