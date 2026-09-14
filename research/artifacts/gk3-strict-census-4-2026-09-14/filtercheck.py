#!/usr/bin/env python3
"""Calibrate the rule-level filters of enum4.py on a shape where everything can be counted.

For every orbit representative of the forward tables of shape ns x nm, compute the number of
rules mu with Dec at that table (projected enumeration with satcensus.build, no Enc part) and
compare with the filters:
  - a table failing F1, or excluded by F3, must carry only the q! trivial rules (symbol
    permutations of the origin coordinate);
  - F4 is a group-level filter (free core), so it is only reported.
Prints one JSON summary with any violations.

Usage: filtercheck.py ns nm q
"""
import itertools, json, math, sys
from pysat.solvers import Solver
import enum4
import satcensus


def main():
    ns, nm, q = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    syms = list(enum4.symmetries(ns, nm))
    S, M = satcensus.labels(ns, nm)
    st = {"shape": f"{ns}x{nm}", "q": q, "orbits": 0, "checked": 0, "violations": [],
          "F4_with_nontrivial_dec": 0}
    for a in enum4.partitions(ns, nm):
        images = {enum4.rgs([a[p] for p in perm]) for perm in syms}
        if a != min(images):
            continue
        st["orbits"] += 1
        bls = enum4.blocks(a, ns, nm)
        f1 = enum4.f1_row_join(bls)
        f3 = f1 and enum4.f3_private_origin(bls, ns)
        f4 = f1 and not f3 and enum4.f4_empty_core(bls)
        if f1 and not f3 and not f4:
            continue
        fwd = [[f"{S[s]}|{M[m]}" for s, m in b] for b in bls]
        cnf, u, _, _ = satcensus.build(ns, nm, q, fwd, None, with_enc=False)
        k = 0
        with Solver(name="cd19", bootstrap_with=cnf.cl) as sol:
            while sol.solve():
                mu = satcensus.decode(sol.get_model(), u)
                k += 1
                sol.add_clause([-u[i][x] for i, x in enumerate(mu)])
        st["checked"] += 1
        if (not f1 or f3) and k != math.factorial(q):
            st["violations"].append({"rgs": a, "F1": f1, "F3": f3, "mus_with_dec": k})
        if f4 and k > math.factorial(q):
            st["F4_with_nontrivial_dec"] += 1
    print(json.dumps(st))


if __name__ == "__main__":
    main()
