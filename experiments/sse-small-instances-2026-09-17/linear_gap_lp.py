#!/usr/bin/env python3
"""Adversarial-weight LP for linear (subgroup) near-optimality of small non-expanding sets
in weighted Cayley graphs of F_2^k.

For a set S (0 in S, |S| = s) put u_x = |S cap (S+x)|/s.  For a probability weight w on
F_2^k \\ {0}, Phi_S(w) = 1 - <w,u> and, for a subgroup H, Phi_H(w) = 1 - w(H).

    T(S, eta, sizes) = max { min_{H : |H| in sizes} Phi_H(w) :  w >= 0, sum w = 1, Phi_S(w) <= eta }

is the worst expansion of the best subgroup set (of the allowed sizes) over *all* weighted
Cayley graphs on F_2^k in which S has expansion <= eta.  T/eta > 1 means S beats every
subgroup on some graph; the maximising w is an explicit weighted Cayley graph.

Local search over S maximises T.  Usage:
    linear_gap_lp.py k s eta size_multipliers iters seed
e.g. linear_gap_lp.py 6 8 0.2 1,2 300 1
"""
import itertools, random, sys, json
import numpy as np
from scipy.optimize import linprog
from sse_cayley import subspaces

def u_vector(k, S):
    N = 1 << k
    Sset = set(S)
    s = len(S)
    u = np.zeros(N)
    for x in range(1, N):
        u[x] = sum(1 for v in S if v ^ x in Sset) / s
    return u

_MAT = {}
def subgroup_matrix(k, sizes):
    key = (k, tuple(sizes))
    if key not in _MAT:
        rows = []
        for size in sizes:
            j = size.bit_length() - 1
            for H in subspaces(k, j):
                r = np.zeros((1 << k) - 1)
                for x in H:
                    if x:
                        r[x - 1] = 1
                rows.append(r)
        _MAT[key] = np.array(rows)
    return _MAT[key]

def T_value(k, S, eta, sizes):
    N = 1 << k
    u = u_vector(k, S)[1:]
    A = subgroup_matrix(k, sizes)
    n = N - 1
    # variables w (n), t ; maximise t
    c = np.zeros(n + 1); c[-1] = -1
    A_ub = np.hstack([A, np.ones((A.shape[0], 1))])      # w(H) + t <= 1
    b_ub = np.ones(A.shape[0])
    A_ub = np.vstack([A_ub, np.concatenate([-u, [0]])])  # -<w,u> <= eta - 1
    b_ub = np.concatenate([b_ub, [eta - 1]])
    A_eq = np.concatenate([np.ones(n), [0]])[None, :]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=[1], bounds=[(0, None)] * n + [(None, None)],
                  method="highs")
    if res.status != 0:
        return None, None
    return -res.fun, res.x[:n]

def local_search(k, s, eta, sizes, iters, seed):
    rng = random.Random(seed)
    N = 1 << k
    S = [0] + rng.sample(range(1, N), s - 1)
    best, w = T_value(k, S, eta, sizes)
    best = best if best is not None else -1
    for it in range(iters):
        S2 = S[:]
        i = rng.randrange(1, s)
        cand = rng.randrange(1, N)
        if cand in S2:
            continue
        S2[i] = cand
        v, w2 = T_value(k, S2, eta, sizes)
        if v is not None and v >= best - 1e-12:
            if v > best + 1e-9:
                print(f"  it {it}: T = {v:.5f}  T/eta = {v/eta:.4f}  S = {sorted(S2)}", flush=True)
            S, best, w = S2, v, w2
    return best, sorted(S), w

if __name__ == "__main__":
    k, s = int(sys.argv[1]), int(sys.argv[2])
    eta = float(sys.argv[3])
    sizes = [s * int(m) for m in sys.argv[4].split(",")]
    iters, seed = int(sys.argv[5]), int(sys.argv[6])
    best, S, w = local_search(k, s, eta, sizes, iters, seed)
    supp = {int(x + 1): round(float(v), 5) for x, v in enumerate(w) if v > 1e-7}
    print(json.dumps(dict(k=k, s=s, eta=eta, sizes=sizes, T=best, ratio=best / eta, S=S, w=supp)))
