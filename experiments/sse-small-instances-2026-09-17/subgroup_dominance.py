#!/usr/bin/env python3
"""Subgroup-dominance constant of a set S in F_2^k (the weight-free form of linear near-optimality).

For S with |S| = s = 2^j put d_S(a) = |S \\ (S+a)|/s  (so 1 - Phi_S = sum_a w_a (1 - d_S(a)) for the
weighted Cayley graph with generator law w).  For a distribution p on subgroups H with |H| = s,
Phi_H = sum_a w_a Pr_p[a not in H] in expectation.  LP duality gives

    sup_w  min_H Phi_H(w) / Phi_S(w)  <=  C(S) := min_p max_{a != 0} Pr_p[a not in H] / d_S(a),

with equality for the mixed (p-averaged) version, and restricting the max to A_theta = {a : d_S(a) <= theta}
gives, for every w with Phi_S(w) <= eta, some subgroup H with Phi_H(w) <= (C_theta(S) + 1/theta) eta.

Usage:
  subgroup_dominance.py exhaustive k s theta            (all S containing 0; small k)
  subgroup_dominance.py search k s theta iters seed     (local search maximising C_theta)
  subgroup_dominance.py ball k theta                    (Hamming ball {0, e_1..e_k}, needs k+1 = 2^j)
"""
import itertools, random, sys, json
import numpy as np
from scipy.optimize import linprog
from sse_cayley import subspaces

_SUB = {}
def subgroup_incidence(k, j):
    if (k, j) not in _SUB:
        Hs = subspaces(k, j)
        M = np.zeros((len(Hs), (1 << k) - 1))
        for i, H in enumerate(Hs):
            for x in H:
                if x:
                    M[i, x - 1] = 1
        _SUB[(k, j)] = (Hs, M)
    return _SUB[(k, j)]

def d_vector(k, S):
    N = 1 << k
    Sset = set(S)
    s = len(S)
    return np.array([sum(1 for v in S if v ^ a not in Sset) / s for a in range(1, N)])

def C_theta(k, S, theta=0.5):
    s = len(S)
    j = s.bit_length() - 1
    assert 1 << j == s
    Hs, M = subgroup_incidence(k, j)
    d = d_vector(k, S)
    idx = [i for i in range(len(d)) if d[i] <= theta + 1e-12]
    nH = len(Hs)
    # variables p (nH), t ; minimise t
    c = np.zeros(nH + 1); c[-1] = 1
    rows, rhs = [], []
    for i in idx:
        miss = 1 - M[:, i]                     # 1[a not in H]
        rows.append(np.concatenate([miss, [-d[i]]]))
        rhs.append(0.0)
    A_ub = np.array(rows) if rows else None
    b_ub = np.array(rhs) if rows else None
    A_eq = np.concatenate([np.ones(nH), [0]])[None, :]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=[1],
                  bounds=[(0, None)] * nH + [(0, None)], method="highs")
    assert res.status == 0, res.message
    return float(res.fun), res.x[:nH], d

def canonical_ok(S):
    return 0 in S

def exhaustive(k, s, theta):
    N = 1 << k
    best = (-1, None)
    hist = {}
    for rest in itertools.combinations(range(1, N), s - 1):
        S = (0,) + rest
        C, _, _ = C_theta(k, S, theta)
        key = round(C, 6)
        hist[key] = hist.get(key, 0) + 1
        if C > best[0] + 1e-9:
            best = (C, S)
            print("new max", round(C, 6), S, flush=True)
    return best, hist

def search(k, s, theta, iters, seed):
    rng = random.Random(seed)
    N = 1 << k
    S = [0] + rng.sample(range(1, N), s - 1)
    C, _, _ = C_theta(k, S, theta)
    for it in range(iters):
        S2 = S[:]
        i = rng.randrange(1, s)
        c = rng.randrange(1, N)
        if c in S2:
            continue
        S2[i] = c
        C2, _, _ = C_theta(k, S2, theta)
        if C2 >= C - 1e-12:
            if C2 > C + 1e-9:
                print(f"it {it}: C = {C2:.6f}  S = {sorted(S2)}", flush=True)
            S, C = S2, C2
    return C, sorted(S)

if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "exhaustive":
        k, s, theta = int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
        best, hist = exhaustive(k, s, theta)
        print(json.dumps(dict(k=k, s=s, theta=theta, max_C=best[0], argmax=best[1],
                              histogram={str(a): b for a, b in sorted(hist.items())})))
    elif mode == "search":
        k, s, theta, iters, seed = int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
        C, S = search(k, s, theta, iters, seed)
        print(json.dumps(dict(k=k, s=s, theta=theta, C=C, S=S)))
    elif mode == "ball":
        k, theta = int(sys.argv[2]), float(sys.argv[3])
        S = [0] + [1 << i for i in range(k)]
        C, p, d = C_theta(k, S, theta)
        print(json.dumps(dict(k=k, theta=theta, C=C, d_min=float(d.min()))))
