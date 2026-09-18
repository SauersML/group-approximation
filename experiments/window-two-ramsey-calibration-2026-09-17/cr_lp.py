"""Coarse Reiter value at the unit ball: v(r) = min over nu in P(B_r) of max_{s in S^{+-1}} ||s nu - nu||_1,
so that CR(1) = min{ r : v(r) <= 1 } (the identity of B_1 contributes 0).

(s nu)(y) = nu(s^{-1} y), left action, as in Moore's convolution mu nu.
Both bounds are certified exactly in Fractions:
  upper: a rational nu on B_r and the exact value max_s ||s nu - nu||_1;
  lower: a rational dual (w, c) with w a probability on the four generators and |c_{s,y}| <= w_s; then for
         every nu, max_s ||s nu - nu|| >= sum_x nu(x) h(x) with h(x) = sum_s (c_{s, s x} - c_{s, x}),
         so v(r) >= min_{x in B_r} h(x).

With a fourth argument M (default 1) the maximum runs over all g in B_M instead of the generators, so that
CR(M) = min{ r : v_M(r) <= 1 }; the dual w is then a probability on B_M minus the identity.

Usage: python3 cr_lp.py GROUP R_MIN R_MAX [M]     (GROUP in {F, F2})
"""
import json
import sys
from fractions import Fraction as Q

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

from window2 import F_ID, F_GENS, f_mul, W_ID, W_GENS, w_mul, ball


def setup(group, R, M=1):
    gens, ident, mul = (F_GENS, F_ID, f_mul) if group == 'F' else (W_GENS, W_ID, w_mul)
    dist = ball(gens, ident, mul, R + M)
    win = [g for g, d in ball(gens, ident, mul, M).items() if d > 0]
    left = [{x: mul(g, x) for x in dist if dist[x] <= R} for g in win]  # g x for x in B_R
    return dist, left


def dual_bound(dist, left, r, denom=10**6):
    K = len(left)
    X = [x for x, d in dist.items() if d <= r]
    Y = sorted({y for x in X for y in [x] + [left[s][x] for s in range(K)]}, key=str)
    yi = {y: i for i, y in enumerate(Y)}
    nc = K * len(Y)
    nv = K + nc + 1  # w_s, c_{s,y}, u
    A = lil_matrix((len(X) + 2 * nc, nv))
    b = np.zeros(len(X) + 2 * nc)
    for row, x in enumerate(X):  # u - sum_s (c_{s,sx} - c_{s,x}) <= 0
        for s in range(K):
            A[row, K + s * len(Y) + yi[left[s][x]]] -= 1
            A[row, K + s * len(Y) + yi[x]] += 1
        A[row, nv - 1] = 1
    row = len(X)
    for s in range(K):
        for j in range(len(Y)):
            col = K + s * len(Y) + j
            A[row, col] = 1
            A[row, s] = -1
            A[row + 1, col] = -1
            A[row + 1, s] = -1
            row += 2
    Aeq = np.zeros((1, nv))
    Aeq[0, :K] = 1
    c = np.zeros(nv)
    c[-1] = -1
    bounds = [(0, None)] * K + [(None, None)] * nc + [(None, None)]
    res = linprog(c, A_ub=A.tocsr(), b_ub=b, A_eq=Aeq, b_eq=[1], bounds=bounds, method='highs')
    xv = res.x
    w = [Q(float(v)).limit_denominator(denom) for v in np.maximum(xv[:K], 0)]
    tot = sum(w)
    w = [v / tot for v in w]
    cc = {}
    for s in range(K):
        for j, y in enumerate(Y):
            v = Q(float(xv[K + s * len(Y) + j])).limit_denominator(denom)
            cc[s, y] = max(-w[s], min(w[s], v))
    h = min(sum(cc[s, left[s][x]] - cc[s, x] for s in range(K)) for x in X)
    return -res.fun, h, [str(v) for v in w]


def primal_bound(dist, left, r, denom=10**6):
    K = len(left)
    X = [x for x, d in dist.items() if d <= r]
    xi = {x: i for i, x in enumerate(X)}
    Y = sorted({y for x in X for y in [x] + [left[s][x] for s in range(K)]}, key=str)
    # ||s nu - nu|| = sum_y |nu(s^-1 y) - nu(y)|; write it over pairs (x, s x): term for y = s x.
    # For each s and each y in Y: coefficient terms. Build preimage map y -> s^{-1} y within X.
    pre = [{} for _ in range(K)]
    for s in range(K):
        for x in X:
            pre[s][left[s][x]] = x
    ny = len(Y)
    nv = len(X) + K * ny + 1
    rows = []
    A = lil_matrix((2 * K * ny + K, nv))
    row = 0
    for s in range(K):
        for j, y in enumerate(Y):
            zc = len(X) + s * ny + j
            for sign in (1, -1):  # sign*(nu(pre) - nu(y)) - z <= 0
                if y in pre[s]:
                    A[row, xi[pre[s][y]]] += sign
                if y in xi:
                    A[row, xi[y]] -= sign
                A[row, zc] = -1
                row += 1
    for s in range(K):
        for j in range(ny):
            A[row, len(X) + s * ny + j] = 1
        A[row, nv - 1] = -1
        row += 1
    Aeq = np.zeros((1, nv))
    Aeq[0, :len(X)] = 1
    c = np.zeros(nv)
    c[-1] = 1
    res = linprog(c, A_ub=A.tocsr(), b_ub=np.zeros(row), A_eq=Aeq, b_eq=[1],
                  bounds=[(0, None)] * (nv - 1) + [(None, None)], method='highs')
    nu = [Q(float(v)).limit_denominator(denom) for v in np.maximum(res.x[:len(X)], 0)]
    tot = sum(nu)
    nu = {x: v / tot for x, v in zip(X, nu)}
    val = max(sum(abs(nu.get(pre[s].get(y), 0) - nu.get(y, 0)) for y in Y) for s in range(K))
    return res.fun, val, sum(1 for v in nu.values() if v)


if __name__ == '__main__':
    group, r0, r1 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    M = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    dist, left = setup(group, r1, M)
    out = []
    for r in range(r0, r1 + 1):
        lp_d, lower, w = dual_bound(dist, left, r)
        lp_p, upper, supp = primal_bound(dist, left, r)
        rec = {'group': group, 'M': M, 'r': r, '|B_r|': sum(1 for d in dist.values() if d <= r),
               'lp_value_dual': lp_d, 'lp_value_primal': lp_p,
               'exact_lower': str(lower), 'exact_upper': str(upper),
               'lower_gt_1': lower > 1, 'upper_le_1': upper <= 1, 'dual_w': w, 'nu_support': supp}
        out.append(rec)
        print(json.dumps(rec), file=sys.stderr, flush=True)
    print(json.dumps(out, indent=1))
