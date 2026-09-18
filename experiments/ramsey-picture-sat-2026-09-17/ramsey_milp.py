"""MILP search for a witness that B_n is NOT 1/2-Ramsey w.r.t. B_m.

Witness (dual form, see research node): E subset of B_n and w = alpha - beta with alpha, beta
probability vectors on A = B_m, such that  sum_a w_a [a g in E] > 1/2  for all g in I_n.
Variables: e_x binary (x in B_n); w_a = alpha_a - beta_a; y_{a,g} = w_a * e_{ag} (exact
linearisation since e is binary and |w_a| <= 1); maximise delta subject to
sum_a y_{a,g} >= 1/2 + delta. Optimum delta* > 0  <=>  B_n is not 1/2-Ramsey w.r.t. B_m.
Floating point: delta* is reported; values near 0 are inconclusive.

usage: python3 ramsey_milp.py {F|F2} m n [time_limit_seconds]
"""
import json
import sys
import time

import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix

import groups


def setup(name, m, n):
    if name == "F":
        gens, ident, mul = groups.F_GENS, groups.F_ID, groups.f_mul
    else:
        gens, ident, mul = groups.W_GENS, groups.W_ID, groups.w_mul
    A = list(groups.ball(gens, ident, mul, m))
    dist = groups.ball(gens, ident, mul, n)
    idx = {g: i for i, g in enumerate(dist)}
    interior = []
    for g in dist:
        row = []
        for a in A:
            h = mul(a, g)
            if h not in idx:
                break
            row.append(idx[h])
        else:
            interior.append(row)
    return A, dist, idx, interior


def solve(name, m, n, tl=600):
    A, dist, idx, interior = setup(name, m, n)
    k, N, I = len(A), len(dist), len(interior)
    # variable layout: e[N] | alpha[k] | beta[k] | y[I*k] | delta
    oe, oa, ob, oy, od = 0, N, N + k, N + 2 * k, N + 2 * k + I * k
    nv = od + 1
    rows = []
    lo, hi = [], []

    def add(coefs, l, h):
        rows.append(coefs)
        lo.append(l)
        hi.append(h)

    add({oa + i: 1 for i in range(k)}, 1, 1)
    add({ob + i: 1 for i in range(k)}, 1, 1)
    for gi, row in enumerate(interior):
        for ai, x in enumerate(row):
            y = oy + gi * k + ai
            # y - (alpha-beta) - (1-e)*? : y <= w + 1 - e  ->  y - a + b + e <= 1
            add({y: 1, oa + ai: -1, ob + ai: 1, oe + x: 1}, -np.inf, 1)
            # y >= w - 1 + e  ->  y - a + b - e >= -1
            add({y: 1, oa + ai: -1, ob + ai: 1, oe + x: -1}, -1, np.inf)
            # -e <= y <= e
            add({y: 1, oe + x: -1}, -np.inf, 0)
            add({y: 1, oe + x: 1}, 0, np.inf)
        c = {oy + gi * k + ai: 1 for ai in range(k)}
        c[od] = -1
        add(c, 0.5, np.inf)
    M = lil_matrix((len(rows), nv))
    for r, coefs in enumerate(rows):
        for j, v in coefs.items():
            M[r, j] = v
    lb = np.zeros(nv)
    ub = np.ones(nv)
    lb[oy:od] = -1
    lb[od], ub[od] = -1, 1
    lb[idx[list(dist)[0]]] = 1  # symmetry: identity in E  (E <-> complement, w <-> -w)
    integrality = np.zeros(nv)
    integrality[oe:oe + N] = 1
    cost = np.zeros(nv)
    cost[od] = -1
    t = time.time()
    r = milp(cost, constraints=LinearConstraint(M.tocsr(), lo, hi), bounds=Bounds(lb, ub),
             integrality=integrality, options={"time_limit": tl, "disp": False})
    res = {"group": name, "m": m, "n": n, "ball": N, "interior": I, "status": int(r.status),
           "message": r.message, "seconds": round(time.time() - t, 1)}
    if r.x is not None:
        res["delta"] = float(r.x[od])
        res["alpha"] = [round(float(v), 6) for v in r.x[oa:oa + k]]
        res["beta"] = [round(float(v), 6) for v in r.x[ob:ob + k]]
        res["E"] = [i for i in range(N) if r.x[i] > 0.5]
    if hasattr(r, "mip_dual_bound") and r.mip_dual_bound is not None:
        res["dual_bound_delta"] = -float(r.mip_dual_bound)
    return res


if __name__ == "__main__":
    name, m, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 600
    res = solve(name, m, n, tl)
    print(json.dumps({k: v for k, v in res.items() if k != "E"}))
    json.dump(res, open(f"milp_{name}_m{m}_n{n}.json", "w"))
