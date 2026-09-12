#!/usr/bin/env python3
"""SAT search for a pair of finite subsets with NO unique product in E_3(q) <= SL_3(Z).

Why: if alpha, beta in k[G] are nonzero with alpha beta = 0, then the pair
(A, B) = (supp alpha, supp beta) has no uniquely represented product, over EVERY
field k (the coefficient at a uniquely represented ab is alpha_a beta_b != 0).
So UNSAT here excludes zero divisors with supports in the given balls over all
fields at once, and SAT gives candidate supports (and shows E_3(q) lacks unique
products).

Host: E_3(q) = <e_ij(q) : i != j> in SL_3(Z); for q >= 3 it lies in Gamma(q),
torsion-free by Minkowski.

Unknowns: A inside B(ra), B inside B(rb). WLOG 1 in A and 1 in B (translate
A -> a^-1 A, B -> B b^-1). Constraint: in every product cell g, the number of
chosen pairs (a, b) with ab = g is 0 or >= 2.

Encoding (python-sat, CaDiCaL): z_p <-> x_a AND y_b for pairs in non-singleton
cells; singleton cells give NOT(x_a AND y_b). Small cells (m <= 10) use the
direct clauses z_k -> OR_{l != k} z_l; larger cells use an exact sequential
counter s_k = [>= 1 among z_1..z_k], d_k = [>= 2 among z_1..z_k], with s_m -> d_m.

Control (--control): adjoins t = diag(-1,-1,1) of order 2; {1,t}{1,t} has no
unique product, so the solver must answer SAT at ra = rb = 1.

Every SAT model is re-checked exactly (verify()) before it is reported.
MSI only. Example:
  python up_sat.py --ra 2 --rb 2 --out e33-up-r22.json --time-limit 600
"""

import argparse
import json
import threading
import time
from collections import defaultdict

IDENT = (1, 0, 0, 0, 1, 0, 0, 0, 1)


def mul(a, b):
    return tuple(sum(a[3 * i + k] * b[3 * k + j] for k in range(3))
                 for i in range(3) for j in range(3))


def elem(i, j, c):
    m = list(IDENT)
    m[3 * i + j] = c
    return tuple(m)


def generators(q, control):
    gens = [elem(i, j, s * q) for i in range(3) for j in range(3) if i != j for s in (1, -1)]
    if control:
        gens.append((-1, 0, 0, 0, -1, 0, 0, 0, 1))
    return gens


def ball(gens, r):
    seen, order, frontier = {IDENT}, [IDENT], [IDENT]
    for _ in range(r):
        nxt = []
        for x in frontier:
            for s in gens:
                y = mul(x, s)
                if y not in seen:
                    seen.add(y)
                    order.append(y)
                    nxt.append(y)
        frontier = nxt
    return order


def verify(Asel, Bsel):
    """Exact check: every product in Asel*Bsel is represented at least twice."""
    if 0 in (len(Asel), len(Bsel)):
        return False, "empty"
    cnt = defaultdict(int)
    for a in Asel:
        for b in Bsel:
            cnt[mul(a, b)] += 1
    ones = sum(1 for v in cnt.values() if v == 1)
    return ones == 0, ("ok" if ones == 0 else "%d uniquely represented products" % ones)


def build(A, B):
    from pysat.formula import CNF
    nA, nB = len(A), len(B)
    cells = defaultdict(list)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            cells[mul(a, b)].append((i, j))
    cnf = CNF()
    top = [nA + nB]

    def new():
        top[0] += 1
        return top[0]

    x = lambda i: 1 + i
    y = lambda j: 1 + nA + j
    cnf.append([x(0)])  # identity index 0 in A
    cnf.append([y(0)])  # identity index 0 in B
    stats = {"cells": len(cells), "singleton_cells": 0, "max_cell": 0}
    for pairs in cells.values():
        m = len(pairs)
        stats["max_cell"] = max(stats["max_cell"], m)
        if m == 1:
            i, j = pairs[0]
            cnf.append([-x(i), -y(j)])
            stats["singleton_cells"] += 1
            continue
        zs = []
        for (i, j) in pairs:
            z = new()
            cnf.extend([[-z, x(i)], [-z, y(j)], [z, -x(i), -y(j)]])
            zs.append(z)
        if m <= 10:
            for k in range(m):
                cnf.append([-zs[k]] + [zs[l] for l in range(m) if l != k])
        else:
            s_prev, d_prev = None, None
            for k, z in enumerate(zs):
                s, d = new(), new()
                if k == 0:
                    cnf.extend([[-z, s], [-s, z], [-d]])
                else:
                    cnf.extend([[-z, s], [-s_prev, s], [-s, s_prev, z],
                                [-z, -s_prev, d], [-d_prev, d],
                                [-d, d_prev, z], [-d, d_prev, s_prev]])
                s_prev, d_prev = s, d
            cnf.append([-s_prev, d_prev])
    return cnf, stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, default=3)
    ap.add_argument("--ra", type=int, required=True)
    ap.add_argument("--rb", type=int, required=True)
    ap.add_argument("--control", action="store_true")
    ap.add_argument("--max-pairs", type=int, default=1500000)
    ap.add_argument("--time-limit", type=float, default=600.0)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    from pysat.solvers import Solver
    t0 = time.time()
    gens = generators(args.q, args.control)
    A, B = ball(gens, args.ra), ball(gens, args.rb)
    rep = {"host": "E_3(%d) in SL_3(Z)%s" % (args.q, " + t=diag(-1,-1,1) CONTROL" if args.control else ""),
           "question": "no-unique-product pair (A,B) with 1 in A, 1 in B, A in B(ra), B in B(rb)",
           "ra": args.ra, "rb": args.rb, "size_A": len(A), "size_B": len(B), "pairs": len(A) * len(B)}
    if len(A) * len(B) > args.max_pairs:
        rep["result"] = "SKIPPED: too many pairs"
        json.dump(rep, open(args.out, "w"), indent=1)
        print(json.dumps(rep))
        return
    cnf, stats = build(A, B)
    rep.update(stats)
    rep.update({"vars": cnf.nv, "clauses": len(cnf.clauses), "build_seconds": round(time.time() - t0, 2)})
    t1 = time.time()
    solver = Solver(name="cadical153", bootstrap_with=cnf.clauses)
    timer = threading.Timer(args.time_limit, solver.interrupt)
    timer.start()
    res = solver.solve_limited(expect_interrupt=True)
    timer.cancel()
    rep["solve_seconds"] = round(time.time() - t1, 2)
    if res is None:
        rep["result"] = "TIMEOUT"
    elif res is False:
        rep["result"] = "UNSAT"
    else:
        model = set(v for v in solver.get_model() if v > 0)
        Asel = [A[i] for i in range(len(A)) if 1 + i in model]
        Bsel = [B[j] for j in range(len(B)) if 1 + len(A) + j in model]
        ok, msg = verify(Asel, Bsel)
        rep.update({"result": "SAT", "verified": ok, "verify_message": msg,
                    "A": [list(a) for a in Asel], "B": [list(b) for b in Bsel]})
    solver.delete()
    json.dump(rep, open(args.out, "w"), indent=1)
    print(json.dumps({k: v for k, v in rep.items() if k not in ("A", "B")}))


if __name__ == "__main__":
    main()
