"""Exact Ramsey profile rho_G(B_1, n) by counterexample-guided SAT (primal form, no enumeration).

rho(n) := min{eps : B_n is eps-Ramsey w.r.t. A = B_1} = max over E subset of B_n of bal(Y_E),
where Y_E = {X_E(g) : g in I_n} is the realized picture collection and
bal(Y) = min over convex combinations v of indicators of Y of (max v - min v)   (Moore, Prop 5.1
and its converse: the nu's supported on I_n push forward to exactly these convex combinations).

Loop: keep a list L of picture collections C (each with an exactly verified bound bal(C) <= b_C).
SAT: find E whose realized collection contains no C in L entirely.
  - found E: b = bal(Y_E) (LP). LB := max(LB, b). Add the support C of an optimal lambda,
    with b_C = exact range of a rationalised lambda (b_C >= bal(C)).
  - UNSAT: every E realizes some C in L, so rho(n) <= max_C b_C =: UB.  Also rho(n) >= LB.
usage: python3 cegar.py {F|F2} n
"""
import json
import sys
import time
from fractions import Fraction as Q

import numpy as np
from pysat.solvers import Cadical153
from scipy.optimize import linprog

from ramsey_sat import setup


def bal(Y, k):
    """LP: minimise s - t over lambda in simplex(Y), t <= v_a <= s. Returns value, lambda."""
    Y = list(Y)
    nY = len(Y)
    # vars: lambda[nY], t, s
    A_ub, b_ub = [], []
    for a in range(k):
        row = [(-1.0 if (P >> a & 1) else 0.0) for P in Y] + [1.0, 0.0]  # t - v_a <= 0
        A_ub.append(row)
        b_ub.append(0.0)
        row = [(1.0 if (P >> a & 1) else 0.0) for P in Y] + [0.0, -1.0]  # v_a - s <= 0
        A_ub.append(row)
        b_ub.append(0.0)
    A_eq = [[1.0] * nY + [0.0, 0.0]]
    c = [0.0] * nY + [-1.0, 1.0]
    r = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=[1.0],
                bounds=[(0, None)] * nY + [(None, None), (None, None)], method="highs")
    return r.fun, dict(zip(Y, r.x[:nY]))


def exact_range(lam, k, den=10 ** 6):
    lamq = {P: Q(round(x * den), den) for P, x in lam.items() if x > 1e-12}
    lamq = {P: x for P, x in lamq.items() if x > 0}
    tot = sum(lamq.values())
    lamq = {P: x / tot for P, x in lamq.items()}
    v = [sum(x for P, x in lamq.items() if P >> a & 1) for a in range(k)]
    return max(v) - min(v), lamq


def run(name, n, log=print):
    dist, idx, interior, k = setup(name, n)
    N = len(dist)
    rvar = {P: N + 1 + P for P in range(1 << k)}
    s = Cadical153()
    for row in interior:
        for P in range(1 << k):
            s.add_clause([(-v if P >> i & 1 else v) for i, v in enumerate(row)] + [rvar[P]])
    L, LB, UB, it = [], Q(0), Q(0), 0
    witness = None
    t0 = time.time()
    while s.solve():
        it += 1
        model = s.get_model()
        val = {abs(l): l > 0 for l in model}
        Y = set()
        for row in interior:
            P = sum(1 << i for i, v in enumerate(row) if val.get(v, False))
            Y.add(P)
        b, lam = bal(Y, k)
        bq, lamq = exact_range(lam, k)
        if b > float(LB) + 1e-12:
            LB = Q(b).limit_denominator(10 ** 4)
            witness = {"E_size": sum(1 for x in range(1, N + 1) if val.get(x, False)),
                       "collection": sorted(Y), "bal": b}
        C = sorted(lamq)
        L.append({"C": C, "bound": str(bq)})
        UB = max(UB, bq)
        s.add_clause([-rvar[P] for P in C])
        if it % 50 == 0:
            log(f"  it {it} LB~{float(LB):.6f} UB {float(UB):.6f} |L| {len(L)}")
    s.delete()
    return {"group": name, "n": n, "ball": N, "interior": len(interior), "iterations": it,
            "rho_lower_approx": float(LB), "rho_upper_exact": str(UB),
            "rho_upper_float": float(UB), "witness": witness, "certificates": L,
            "seconds": round(time.time() - t0, 1)}


if __name__ == "__main__":
    name, n = sys.argv[1], int(sys.argv[2])
    res = run(name, n)
    print(json.dumps({k: v for k, v in res.items() if k != "certificates"}), flush=True)
    json.dump(res, open(f"cegar_{name}_n{n}.json", "w"), indent=1)
