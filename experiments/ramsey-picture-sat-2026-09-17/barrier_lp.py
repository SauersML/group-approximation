"""Fractional relaxation of the 1/3 barrier (third_barrier.py).

T f (g) = f(x0^-1 g) - f(x0 g) + 2 f(x1 g) - 2 f(x1^-1 g)   (= 3 * sum_a w_a f(a g)).
M_n := min{ max f : f : B_n -> [0, inf), (T f)(g) >= 1 for all g in I_n }.
The {0,1} barrier at radius n is feasible only if M_n <= 1.  If G is amenable, M_n -> inf
(an invariant mean kills T f, and a bounded f with T f >= 1 on I_n for all n gives, by
compactness, a global bounded f with T f >= 1).  The LP is floating; only "exact_M" (an
upper bound M_n <= exact_M, re-verified in Fractions) is a certificate.
With w = 'half' (the F_2 global witness direction): T f(g) = f(x1 g) + f(x1^-1 g) - f(x0 g) - f(x0^-1 g)
(= 2 * sum_a w_a f(a g)).  In both cases V_n(w) := max_{f: B_n -> [0,1]} min_{g in I_n} sum_a w_a f(a g)
equals 1/(s M_n) (s = 3 or 2; add a constant to f, as sum_a w_a = 0), a lower bound for the
function (Moore R-tilde) profile.  Exactness: the LP optimum f is rationalised and T f >= 1 and
max f = M are re-checked with Fractions ("exact_M").
usage: python3 barrier_lp.py {F|F2|Z2} nmin nmax [third|half]
"""
import json
import sys
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

from ramsey_sat import setup

from fractions import Fraction as Q

COEFS = {"third": [0, -1, 1, 2, -2], "half": [0, -1, -1, 1, 1]}  # A order: e, x0, x0^-1, x1, x1^-1
COEF = COEFS["third"]


def lp(name, n):
    t = time.time()
    dist, idx, interior, k = setup(name, n)
    N = len(dist)
    rows, cols, vals = [], [], []
    for r, row in enumerate(interior):
        for c, v in zip(COEF, row):
            if c:
                rows.append(r)
                cols.append(v - 1)
                vals.append(-c)  # -(T f) <= -1
    m = len(interior)
    # variable N is M (the max); f_x - M <= 0
    for x in range(N):
        rows.append(m + x)
        cols.append(x)
        vals.append(1.0)
        rows.append(m + x)
        cols.append(N)
        vals.append(-1.0)
    A = coo_matrix((vals, (rows, cols)), shape=(m + N, N + 1)).tocsr()
    b = np.concatenate([-np.ones(m), np.zeros(N)])
    c = np.zeros(N + 1)
    c[N] = 1.0
    r = linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)] * (N + 1), method="highs")
    exact = None
    if r.status == 0:
        for den, scale in ((10 ** 4, 1), (10 ** 7, 1 + 1e-6), (10 ** 7, 1 + 1e-4), (10 ** 7, 1.001)):
            fq = [Q(max(x, 0.0) * scale).limit_denominator(den) for x in r.x[:N]]
            if all(sum(Q(c) * fq[v - 1] for c, v in zip(COEF, row)) >= 1 for row in interior):
                exact = str(max(fq))
                break
    return {"group": name, "n": n, "ball": N, "interior": m,
            "M_n": (r.fun if r.status == 0 else None), "exact_M": exact, "status": r.status,
            "seconds": round(time.time() - t, 1)}


if __name__ == "__main__":
    name, a, b = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    wname = sys.argv[4] if len(sys.argv) > 4 else "third"
    COEF[:] = COEFS[wname]
    out = []
    for n in range(a, b + 1):
        rec = lp(name, n)
        rec["w"] = wname
        print(json.dumps(rec), flush=True)
        out.append(rec)
        json.dump(out, open(f"barrier_lp_{wname}_{name}_n{a}-{b}.json", "w"), indent=1)
