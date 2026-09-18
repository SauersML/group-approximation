"""Dual certificate for the extremal CEGAR witness: the realized collection Y_E of a set E
with bal(Y_E) = rho, and probability measures alpha, beta on B_1 maximising
min_{P in Y_E} (alpha - beta)(P).  (If that minimum is z > 0 then for every nu supported on
I_n, sum_a (alpha-beta)(a) a nu(E) >= z, so max_a a nu(E) - min_a a nu(E) >= z.)
usage: python3 witness_dual.py {F|F2} n
"""
import json
import sys

from scipy.optimize import linprog

NAMES = ["e", "x0", "x0^-1", "x1", "x1^-1"]


def dual(Y, k):
    A_ub, b_ub = [], []
    for P in Y:
        row = [(-1.0 if P >> i & 1 else 0.0) for i in range(k)]
        row += [(1.0 if P >> i & 1 else 0.0) for i in range(k)] + [1.0]
        A_ub.append(row)
        b_ub.append(0.0)
    A_eq = [[1.0] * k + [0.0] * k + [0.0], [0.0] * k + [1.0] * k + [0.0]]
    r = linprog([0.0] * (2 * k) + [-1.0], A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=[1, 1],
                bounds=[(0, 1)] * (2 * k) + [(None, None)], method="highs")
    return -r.fun, r.x[:k], r.x[k:2 * k]


if __name__ == "__main__":
    name, n = sys.argv[1], int(sys.argv[2])
    res = json.load(open(f"cegar_{name}_n{n}.json"))
    w = res["witness"]
    k = 5
    z, a, b = dual(w["collection"], k)
    print("rho", res["rho_upper_exact"], "witness bal", w["bal"], "|E|", w["E_size"],
          "#pictures", len(w["collection"]))
    print("dual min (alpha-beta)(P) =", round(z, 6))
    print("alpha", {NAMES[i]: round(a[i], 4) for i in range(k) if a[i] > 1e-9})
    print("beta", {NAMES[i]: round(b[i], 4) for i in range(k) if b[i] > 1e-9})
    for P in w["collection"]:
        print("  picture", [NAMES[i] for i in range(k) if P >> i & 1])
