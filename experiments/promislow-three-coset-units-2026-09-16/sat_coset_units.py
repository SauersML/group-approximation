#!/usr/bin/env python3
"""SAT search for units of F_2[P] with prescribed coset support (P = Promislow group).

Search space.  u = sum over cosets c in CU of f_c * rep_c, each f_c supported in the box
BU = [-RU..RU]^3 of L = <x,y,z> (engine coordinates x^i y^j z^k); inverse candidate
v = sum over all four cosets of g_d * rep_d, each g_d supported in BV = [-RV..RV]^3.
Constraints: u v = 1 in F_2[P] (every coefficient of the product), and every piece f_c
(c in CU) is nonzero.
  mode 3coset: CU = {e, A, B} (u = p + q a + r b).  All three pieces nonzero is exactly
               "not a two-coset element"; two-coset units are trivial (they lie in the group
               ring of an index-2 poly-Z subgroup), so a solution is a nontrivial unit.
  mode 4coset: CU = {e, A, B, C}, all four pieces nonzero (validation: must find Gardam's unit).
Method.  Tseitin CNF: one AND variable per product pair, XOR chains per group element,
solved with CaDiCaL (pysat).  Every SAT model is re-verified exactly with engine.gmul and
engine.det_right_mult (mod 2).  UNSAT means: no unit u with supp(u) in the stated set has
an inverse supported in BV^4 (a statement about the support pair only).
Usage: sat_coset_units.py MODE RU RV [MAXSOL]
"""
import sys, json, time, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from engine import gmul, det_right_mult, ONE, k4mul, act, COC, addm
from pysat.solvers import Solver

mode = sys.argv[1] if len(sys.argv) > 1 else '3coset'
RU = int(sys.argv[2]) if len(sys.argv) > 2 else 1
RV = int(sys.argv[3]) if len(sys.argv) > 3 else 2
MAXSOL = int(sys.argv[4]) if len(sys.argv) > 4 else 3
CU = 'eAB' if mode == '3coset' else 'eABC'
rng = lambda R: range(-R, R + 1)
BU = [(i, j, k) for i in rng(RU) for j in rng(RU) for k in rng(RU)]
BV = [(i, j, k) for i in rng(RV) for j in rng(RV) for k in rng(RV)]

nv = [0]
def new():
    nv[0] += 1
    return nv[0]
U = {(c, m): new() for c in CU for m in BU}
V = {(d, n): new() for d in 'eABC' for n in BV}
clauses = []
prod = {}
for (c, m), xu in U.items():
    for (d, n), xv in V.items():
        g = (k4mul(c, d), addm(addm(m, act(c, n)), COC[(c, d)]))
        w = new()
        clauses += [[-w, xu], [-w, xv], [w, -xu, -xv]]
        prod.setdefault(g, []).append(w)
one = ('e', (0, 0, 0))
assert one in prod
def xor_chain(lits, rhs):
    # constrain XOR(lits) = rhs
    acc = lits[0]
    for l in lits[1:]:
        t = new()
        clauses.extend([[-t, acc, l], [-t, -acc, -l], [t, -acc, l], [t, acc, -l]])
        acc = t
    clauses.append([acc] if rhs else [-acc])
for g, lits in prod.items():
    xor_chain(lits, 1 if g == one else 0)
for c in CU:
    clauses.append([U[(c, m)] for m in BU])

info = {"mode": mode, "u_cosets": CU, "u_box_radius": RU, "v_box_radius": RV,
        "u_vars": len(U), "v_vars": len(V), "total_vars": nv[0], "clauses": len(clauses)}
t0 = time.time()
sols = []
with Solver(name='cadical153', bootstrap_with=clauses) as S:
    while len(sols) < MAXSOL and S.solve():
        model = set(l for l in S.get_model() if l > 0)
        u = {k: 1 for k, x in U.items() if x in model}
        v = {k: 1 for k, x in V.items() if x in model}
        ok_inv = gmul(u, v, 2) == ONE
        nrd = det_right_mult(u, 2)
        ok_nrd = nrd == {(0, 0, 0): 1}
        sols.append({"support_u": len(u), "support_v": len(v), "uv_is_1": ok_inv, "nrd_is_1": ok_nrd,
                     "u": sorted([c, list(m)] for (c, m) in u)})
        S.add_clause([-U[k] for k in u] + [U[k] for k in U if k not in u])  # block this u
    status = "SAT" if sols else "UNSAT"
info.update({"result": status, "solutions_listed": len(sols), "seconds": round(time.time() - t0, 1)})
print(json.dumps(info))
for s in sols:
    print(json.dumps(s))
