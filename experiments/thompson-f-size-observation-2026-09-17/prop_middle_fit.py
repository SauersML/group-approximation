"""Proportional-middle padding: numerical feasibility (scouting, floating point).

Same tops as equal_middle_lp.py (complete depth-d tops on roots 0..m, INF atoms at
the two extreme leaves, one stable level elsewhere), but the middle weight vector
of s is only required to be proportional to one common vector c:
    weight(piece_p(s)) = f_s * c_p   for p = 1..m+d-1.
Unknowns log w (leaves), log f_s, log c_p; least squares on relative residuals,
many random restarts.  Output: best residual; ~0 means feasible (then an exact
rational solution is sought separately).
"""
import sys

import numpy as np
from scipy.optimize import least_squares

from level_search import monomial_set
from equal_middle_lp import antichain, leaves


def build(m, d, ends="both"):
    S = monomial_set(m, d)
    L = leaves(m, d)
    if ends == "left":
        L = L + [(m, "1" * d)]
    idx = {v: i for i, v in enumerate(L)}
    rows = []  # (si, p, [leaf indices])
    for si, w in enumerate(S):
        pcs = antichain(m, w)
        mid = pcs[1:-1] if ends == "both" else pcs[1:]
        for p, (a, q) in enumerate(mid, start=1):
            ids = [idx[(b, r)] for (b, r) in L if b == a and r.startswith(q)]
            rows.append((si, p, ids))
    return S, L, rows


def fit(m, d, restarts=40, seed=0, ends="both"):
    S, L, rows = build(m, d, ends)
    nw, ns, nc = len(L), len(S), m + d - 1 + (ends == "left")
    rng = np.random.default_rng(seed)

    def resid(x):
        w = np.exp(x[:nw])
        f = np.exp(x[nw:nw + ns])
        c = np.exp(x[nw + ns:])
        out = []
        for si, p, ids in rows:
            lhs = w[ids].sum()
            rhs = f[si] * c[p - 1]
            out.append(np.log(lhs) - np.log(rhs))
        return np.array(out)

    best = None
    for _ in range(restarts):
        x0 = rng.normal(0, 1.5, nw + ns + nc)
        r = least_squares(resid, x0, method="lm" if len(rows) >= len(x0) else "trf", max_nfev=20000)
        val = float(np.max(np.abs(r.fun)))
        if best is None or val < best[0]:
            best = (val, r.x)
    return best, S, L


if __name__ == "__main__":
    ends = sys.argv[1]
    cases = [tuple(int(x) for x in c.split(",")) for c in sys.argv[2:]]
    for (m, d) in cases:
        (val, x), S, L = fit(m, d, ends=ends)
        nw = len(L)
        w = np.exp(x[:nw])
        print(f"m={m} d={d}: best max |log residual| = {val:.3e}; min/max leaf weight = "
              f"{w.min() / w.max():.3e}", flush=True)
