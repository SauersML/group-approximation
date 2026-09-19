"""Folded local search: f(-x) = -f(x), pins f(chi_a) = xi_a, minimize weighted cut.

State: b[r] for folded reps r < N/2 (top bit clear), True = +1; f(x) = b[x] for x < N/2,
f(x) = not b[x ^ full] otherwise.  Single-class flips with exact incremental gains
(each class has 2K incident edges).  Returns a feasible folded f, so its cut vector
is a valid adversary column (upper-bound side).
"""
import numpy as np
from scipy.sparse import csr_matrix


def incidence(S):
    if "inc" in S:
        return S["inc"]
    N, full = S["N"], S["full"]
    half = N >> 1
    ex = S["ex"]; ey = ex ^ (np.int64(1) << S["ej"])
    rx = np.where(ex < half, ex, ex ^ full); ry = np.where(ey < half, ey, ey ^ full)
    E = len(ex)
    rows = np.r_[rx, ry]; cols = np.r_[np.arange(E), np.arange(E)]
    M = csr_matrix((np.ones(2 * E, dtype=np.int8), (rows, cols)), shape=(half, E))
    S["inc"] = (M.indptr, M.indices, ex, ey, half)
    return S["inc"]


def full_f(S, b):
    N, full = S["N"], S["full"]
    half = N >> 1
    xs = np.arange(N, dtype=np.int64)
    return np.where(xs < half, b[np.where(xs < half, xs, 0)], ~b[np.where(xs < half, 0, xs ^ full)])


def pinned(S, xi):
    N, full = S["N"], S["full"]
    half = N >> 1
    fix = {}
    for a, m in enumerate(S["prim"]):
        m = int(m)
        val = not ((int(xi) >> a) & 1)       # True = +1
        if m < half:
            fix[m] = val
        else:
            fix[m ^ full] = not val
    return fix


_LS = None


def _ls_lib():
    global _LS
    if _LS is None:
        import ctypes, os, subprocess, tempfile
        src = os.path.join(os.path.dirname(os.path.abspath(__file__)), "hadk_ls.c")
        out = os.path.join(os.environ.get("HADK_BUILD", tempfile.gettempdir()), "hadk_ls.so")
        if not os.path.exists(out) or os.path.getmtime(out) < os.path.getmtime(src):
            subprocess.check_call(["gcc", "-O2", "-shared", "-fPIC", "-o", out, src])
        L = ctypes.CDLL(out)
        P = np.ctypeslib.ndpointer
        L.local_search.restype = ctypes.c_double
        L.local_search.argtypes = [ctypes.c_int, ctypes.c_int, P(np.int32), P(np.int32), P(np.uint8),
                                   P(np.float64), P(np.int32), P(np.int32), P(np.uint8), P(np.uint8),
                                   ctypes.c_int]
        _LS = L
    return _LS


def local_search_c(S, w, xi, b0, rng=None, max_pass=200):
    """same contract as local_search, 1-opt sweeps in C."""
    indptr, indices, ex, ey, half = incidence(S)
    if "ls_arrays" not in S:
        full = S["full"]
        rx = np.where(ex < half, ex, ex ^ full).astype(np.int32)
        ry = np.where(ey < half, ey, ey ^ full).astype(np.int32)
        par = ((ex >= half) ^ (ey >= half)).astype(np.uint8)
        S["ls_arrays"] = (rx, ry, par, indptr.astype(np.int32), indices.astype(np.int32))
    rx, ry, par, ip, ii = S["ls_arrays"]
    fix = pinned(S, xi)
    b = b0.astype(np.uint8).copy()
    fixed = np.zeros(half, dtype=np.uint8)
    for r, v in fix.items():
        b[r] = 1 if v else 0; fixed[r] = 1
    wv = np.ascontiguousarray(w, dtype=np.float64)
    val = _ls_lib().local_search(half, len(rx), rx, ry, par, wv, ip, ii, fixed, b, max_pass)
    bb = b.astype(bool)
    cut = (bb[rx] ^ bb[ry] ^ par.astype(bool))
    return float(val), cut, bb


def local_search(S, w, xi, b0, rng=None, max_pass=200):
    return local_search_c(S, w, xi, b0, rng, max_pass)


def local_search_py(S, w, xi, b0, rng=None, max_pass=50):
    """reference pure-numpy version (slow at k = 4)."""
    indptr, indices, ex, ey, half = incidence(S)
    fix = pinned(S, xi)
    b = b0.copy()
    for r, v in fix.items():
        b[r] = v
    fixed = np.zeros(half, dtype=bool); fixed[list(fix)] = True
    f = full_f(S, b)
    cut = f[ex] != f[ey]
    for _ in range(max_pass):
        sw = np.where(cut, w, -w)
        gain = np.add.reduceat(sw[indices], indptr[:-1])
        gain[fixed] = -np.inf
        cand = np.flatnonzero(gain > 1e-13)
        if len(cand) == 0:
            break
        if rng is not None:
            rng.shuffle(cand)
        for r in cand:
            s, t = indptr[r], indptr[r + 1]
            es = indices[s:t]
            # recompute exact gain for r
            g = np.where(cut[es], w[es], -w[es]).sum()
            if g <= 1e-13:
                continue
            b[r] = ~b[r]
            cut[es] = ~cut[es]
    f = full_f(S, b)
    cut = f[ex] != f[ey]
    return float(cut @ w), cut, b
