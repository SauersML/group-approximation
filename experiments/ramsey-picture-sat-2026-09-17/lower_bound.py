"""Exact lower bound rho_G(B_1, n) >= t from a closed non-balanced family.
SAT (ramsey_sat.realizable) gives E subset B_n whose realized pictures lie in the family; the
dual LP (witness_dual.dual) on the realized collection Y gives alpha, beta; they are
rationalised and min_{P in Y} (alpha - beta)(P) >= t is checked with Fractions.  Then for every
nu on I_n: max_a a nu(E) - min_a a nu(E) >= sum_a (alpha-beta)_a a nu(E) >= t.
usage: python3 lower_bound.py {F|F2|Z2} n families_file family_index t
"""
import json
import sys
from fractions import Fraction as Q

from ramsey_sat import realizable, setup
from witness_dual import dual


def main(name, n, ffile, j, t):
    fam = json.load(open(ffile))["maximal"][j]
    dist, idx, interior, k = setup(name, n)
    ok, model = realizable(interior, k, fam)
    if not ok:
        print(json.dumps({"group": name, "n": n, "family": j, "sat": False}))
        return
    val = {abs(l): l > 0 for l in model}
    Y = sorted({sum(1 << i for i, v in enumerate(row) if val.get(v, False)) for row in interior})
    z, a, b = dual(Y, k)
    best = None
    for den in (2, 3, 4, 6, 12, 60, 360, 2520):
        aq = [Q(x).limit_denominator(den) for x in a]
        bq = [Q(x).limit_denominator(den) for x in b]
        if sum(aq) != 1 or sum(bq) != 1 or min(aq + bq) < 0:
            continue
        m = min(sum(aq[i] - bq[i] for i in range(k) if P >> i & 1) for P in Y)
        if m >= t:
            best = {"alpha": [str(x) for x in aq], "beta": [str(x) for x in bq], "min": str(m)}
            break
    rec = {"group": name, "n": n, "family": j, "sat": True, "realized": Y,
           "E_size": sum(1 for v in idx.values() if val.get(v, False)),
           "dual_float": z, "exact": best}
    print(json.dumps(rec))
    json.dump(rec, open(f"lower_bound_{name}_n{n}_fam{j}.json", "w"), indent=1)


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), Q(sys.argv[5]))
