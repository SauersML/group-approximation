#!/usr/bin/env python3
"""Characteristic-free support check on (S, T).

If u is a unit over any field with supp(u) = S' subset S, supp(u^-1) = T' subset T,
then 1 lies in S'T' and no product k != 1 is represented exactly once
(its coefficient in u u^-1 would be one nonzero product u_i v_j).
Query: is there such (S', T') with |S'| >= 2 and (g_1 not in S' or g_2 not in S')?
UNSAT means every nontrivial unit on (S, T) has u_1, u_2 != 0 (Gardam's case (1,2)).
A second query drops the g_1/g_2 condition, as a sanity check that the full pair is found.
"""
import json
from collections import defaultdict
from z3 import Bool, Solver, Or, Not, If, Sum, And, PbGe, sat

sysd = json.load(open("system.json"))
prod, K, eid = sysd["prod"], sysd["K"], sysd["eid"]
n = 21
reps = defaultdict(list)
for i in range(n):
    for j in range(n):
        reps[prod[i][j]].append((i, j))

def query(extra):
    s = [Bool(f"s{i}") for i in range(n)]
    t = [Bool(f"t{j}") for j in range(n)]
    sol = Solver()
    sol.add(PbGe([(s[i], 1) for i in range(n)], 2))
    for k, lst in reps.items():
        c = Sum([If(And(s[i], t[j]), 1, 0) for i, j in lst])
        sol.add(c >= 1 if k == eid else c != 1)
    extra(sol, s, t)
    r = sol.check()
    out = {"result": str(r)}
    if r == sat:
        m = sol.model()
        out["S'"] = [i for i in range(n) if m.evaluate(s[i])]
        out["T'"] = [j for j in range(n) if m.evaluate(t[j])]
    return out

print("proper (g_1 or g_2 missing):", query(lambda sol, s, t: sol.add(Or(Not(s[0]), Not(s[1])))))
print("sanity, no restriction:", query(lambda sol, s, t: None))
