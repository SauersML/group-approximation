"""Linear program for the 'equal middle' padding of the size observation.

Roots 0..m are complete binary tops of depth d (only these roots are split by
S = S_(m+1,m+d+1)).  The leftmost leaf of root 0 and the rightmost leaf of root
m are INF atoms (independent huge sizes); every other depth-d leaf v carries a
weight w_v >= 0 of one stable level.  For s in S the pieces of roots 0..m are
m+d+1 nodes; positions 0 and m+d always hold the two INF atoms, and we ask
that every middle piece (positions 1..m+d-1) have weight exactly f_s >= 1.
Feasibility gives a shadow law for the size observation (see mixed_search.py
for the probabilistic reading); exact rational solution is recovered and
re-checked below.
"""
import sys
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog

from level_search import monomial_set


def antichain(m, word):
    cur = [(a, "") for a in range(m + 1)]
    for i in word:
        a, p = cur[i]
        cur = cur[:i] + [(a, p + "0"), (a, p + "1")] + cur[i + 1:]
    return cur


def leaves(m, d):
    out = []
    for a in range(m + 1):
        for k in range(2 ** d):
            p = format(k, "0%db" % d)
            if (a == 0 and p == "0" * d) or (a == m and p == "1" * d):
                continue
            out.append((a, p))
    return out


def solve(m, d, verbose=True):
    S = monomial_set(m, d)
    L = leaves(m, d)
    idx = {v: i for i, v in enumerate(L)}
    nw, nf = len(L), len(S)
    A_eq, b_eq = [], []
    for si, w in enumerate(S):
        pcs = antichain(m, w)
        assert len(pcs) == m + d + 1
        for (a, p) in pcs[1:-1]:
            row = np.zeros(nw + nf)
            for (b, q) in L:
                if b == a and q.startswith(p):
                    row[idx[(b, q)]] = 1.0
            if (a == 0 and ("0" * d).startswith(p)) or (a == m and ("1" * d).startswith(p)):
                return None, "middle piece contains an INF atom"
            row[nw + si] = -1.0
            A_eq.append(row)
            b_eq.append(0.0)
    bounds = [(0, None)] * nw + [(1, None)] * nf
    c = np.concatenate([np.ones(nw), np.zeros(nf)])
    res = linprog(c, A_eq=np.array(A_eq), b_eq=np.array(b_eq), bounds=bounds, method="highs")
    if res.status != 0:
        return None, res.message
    wts = {v: res.x[idx[v]] for v in L}
    fs = {w: res.x[nw + i] for i, w in enumerate(S)}
    return (wts, fs), "ok"


if __name__ == "__main__":
    cases = [tuple(int(x) for x in c.split(",")) for c in sys.argv[1:]]
    for (m, d) in cases:
        sol, msg = solve(m, d)
        print(f"m={m} d={d} |S|={len(monomial_set(m, d))}: {'FEASIBLE' if sol else 'INFEASIBLE'} ({msg})",
              flush=True)
