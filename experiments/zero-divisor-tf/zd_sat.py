#!/usr/bin/env python3
"""Gardam-style SAT census for zero divisors in F_p[H], H torsion-free in SL_3(Z).

Host: E_3(q) = <e_ij(q) : i != j> in SL_3(Z). For q >= 3 it lies in the
principal congruence subgroup Gamma(q), which is torsion-free by Minkowski.

Unknowns: alpha supported in A = B(ra) and beta supported in B = B(rb), both
balls for the generators e_ij(+-q). The census asks for alpha beta = 0 with
alpha != 0 and beta != 0. There is no symmetry breaking, so UNSAT means no
such pair has supports inside these balls.

Encodings:
  p = 2: pycryptosat. z_ij <-> x_i AND y_j, and one native XOR clause per
         product cell with rhs 0. A singleton cell forces NOT(x_i AND y_j).
  p = 3: python-sat (CaDiCaL). Each element has two one-hot bits (coefficient
         1 or 2). Each pair yields exclusive bits u = [prod = 1], w = [prod = 2],
         and each cell runs a mod-3 counter that must end in state 0.
Control (--control): adds t = diag(-1,-1,1), of order 2. Then (1+t)(1-t) = 0,
so the solver must answer SAT at ra = rb = 1. This tests the encoding end to
end.

Every SAT model is recomputed with exact integer matrix products (verify()),
independently of the encoder, before anything is reported.

MSI only. Example:
  python zd_sat.py --p 2 --ra 2 --rb 2 --out e33-p2-r22.json
"""

import argparse
import json
import sys
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
    gens = []
    for i in range(3):
        for j in range(3):
            if i != j:
                gens.append(elem(i, j, q))
                gens.append(elem(i, j, -q))
    if control:
        gens.append((-1, 0, 0, 0, -1, 0, 0, 0, 1))
    return gens


def ball(gens, r):
    seen = {IDENT}
    order = [IDENT]
    frontier = [IDENT]
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


def cells_of(A, B):
    cells = defaultdict(list)
    nB = len(B)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            cells[mul(a, b)].append(i * nB + j)
    return cells


def verify(A, B, xa, yb, p):
    """Exact recomputation of alpha*beta mod p; xa, yb map index -> coefficient."""
    if not any(c % p for c in xa.values()) or not any(c % p for c in yb.values()):
        return False, "alpha or beta is zero"
    prod = defaultdict(int)
    for i, ca in xa.items():
        for j, cb in yb.items():
            k = mul(A[i], B[j])
            prod[k] = (prod[k] + ca * cb) % p
    bad = [k for k, v in prod.items() if v % p]
    return (not bad), ("ok" if not bad else "nonzero coefficient at %d cells" % len(bad))


def solve_p2(A, B, cells, threads):
    from pycryptosat import Solver
    s = Solver(threads=threads)
    nA, nB = len(A), len(B)
    xv = lambda i: 1 + i
    yv = lambda j: 1 + nA + j
    nxt = 1 + nA + nB
    nclauses = 0
    for pairs in cells.values():
        if len(pairs) == 1:
            i, j = divmod(pairs[0], nB)
            s.add_clause([-xv(i), -yv(j)])
            nclauses += 1
            continue
        zs = []
        for pr in pairs:
            i, j = divmod(pr, nB)
            z = nxt
            nxt += 1
            s.add_clause([-z, xv(i)])
            s.add_clause([-z, yv(j)])
            s.add_clause([z, -xv(i), -yv(j)])
            zs.append(z)
        s.add_xor_clause(zs, False)
        nclauses += 3 * len(zs) + 1
    s.add_clause([xv(i) for i in range(nA)])
    s.add_clause([yv(j) for j in range(nB)])
    sat, model = s.solve()
    if not sat:
        return False, None, None, nxt - 1, nclauses
    xa = {i: 1 for i in range(nA) if model[xv(i)]}
    yb = {j: 1 for j in range(nB) if model[yv(j)]}
    return True, xa, yb, nxt - 1, nclauses


def solve_p3(A, B, cells):
    from pysat.solvers import Solver
    clauses = []
    nA, nB = len(A), len(B)
    counter = [0]

    def new():
        counter[0] += 1
        return counter[0]

    a1 = [new() for _ in range(nA)]
    a2 = [new() for _ in range(nA)]
    b1 = [new() for _ in range(nB)]
    b2 = [new() for _ in range(nB)]
    for i in range(nA):
        clauses.append([-a1[i], -a2[i]])
    for j in range(nB):
        clauses.append([-b1[j], -b2[j]])
    clauses.append(a1 + a2)
    clauses.append(b1 + b2)

    def conj(x, y):
        v = new()
        clauses.extend([[-v, x], [-v, y], [v, -x, -y]])
        return v

    def disj(x, y):
        v = new()
        clauses.extend([[v, -x], [v, -y], [-v, x, y]])
        return v

    for pairs in cells.values():
        if len(pairs) == 1:
            i, j = divmod(pairs[0], nB)
            for s_ in (a1[i], a2[i]):
                for t_ in (b1[j], b2[j]):
                    clauses.append([-s_, -t_])
            continue
        state = [new(), new(), new()]
        clauses.extend([[state[0]], [-state[1]], [-state[2]]])
        for pr in pairs:
            i, j = divmod(pr, nB)
            u = disj(conj(a1[i], b1[j]), conj(a2[i], b2[j]))
            w = disj(conj(a1[i], b2[j]), conj(a2[i], b1[j]))
            nstate = [new(), new(), new()]
            for k in range(3):
                clauses.append([-state[k], u, w, nstate[k]])
                clauses.append([-state[k], -u, nstate[(k + 1) % 3]])
                clauses.append([-state[k], -w, nstate[(k + 2) % 3]])
            for k in range(3):
                for l in range(k + 1, 3):
                    clauses.append([-nstate[k], -nstate[l]])
            state = nstate
        clauses.append([state[0]])
    name = "cadical153"
    try:
        solver = Solver(name=name, bootstrap_with=clauses)
    except Exception:
        name = "g4"
        solver = Solver(name=name, bootstrap_with=clauses)
    sat = solver.solve()
    if not sat:
        solver.delete()
        return False, None, None, counter[0], len(clauses)
    model = set(v for v in solver.get_model() if v > 0)
    solver.delete()
    xa = {i: (1 if a1[i] in model else 2) for i in range(nA) if a1[i] in model or a2[i] in model}
    yb = {j: (1 if b1[j] in model else 2) for j in range(nB) if b1[j] in model or b2[j] in model}
    return True, xa, yb, counter[0], len(clauses)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--p", type=int, choices=(2, 3), required=True)
    ap.add_argument("--q", type=int, default=3)
    ap.add_argument("--ra", type=int, required=True)
    ap.add_argument("--rb", type=int, required=True)
    ap.add_argument("--control", action="store_true")
    ap.add_argument("--threads", type=int, default=1)
    ap.add_argument("--max-pairs", type=int, default=3000000)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    t0 = time.time()
    gens = generators(args.q, args.control)
    A = ball(gens, args.ra)
    B = ball(gens, args.rb)
    rep = {"host": "E_3(%d) in SL_3(Z)%s" % (args.q, " + t=diag(-1,-1,1) CONTROL" if args.control else ""),
           "p": args.p, "ra": args.ra, "rb": args.rb, "size_A": len(A), "size_B": len(B),
           "pairs": len(A) * len(B)}
    if len(A) * len(B) > args.max_pairs:
        rep["result"] = "SKIPPED: too many pairs"
        json.dump(rep, open(args.out, "w"), indent=1)
        print(json.dumps(rep))
        return
    cells = cells_of(A, B)
    rep["cells"] = len(cells)
    rep["singleton_cells"] = sum(1 for v in cells.values() if len(v) == 1)
    rep["build_seconds"] = round(time.time() - t0, 2)
    t1 = time.time()
    if args.p == 2:
        sat, xa, yb, nvars, ncl = solve_p2(A, B, cells, args.threads)
    else:
        sat, xa, yb, nvars, ncl = solve_p3(A, B, cells)
    rep.update({"vars": nvars, "clauses": ncl, "solve_seconds": round(time.time() - t1, 2)})
    if sat:
        ok, msg = verify(A, B, xa, yb, args.p)
        rep["result"] = "SAT"
        rep["verified"] = ok
        rep["verify_message"] = msg
        rep["alpha"] = [[list(A[i]), c] for i, c in sorted(xa.items())]
        rep["beta"] = [[list(B[j]), c] for j, c in sorted(yb.items())]
    else:
        rep["result"] = "UNSAT"
    json.dump(rep, open(args.out, "w"), indent=1)
    print(json.dumps({k: v for k, v in rep.items() if k not in ("alpha", "beta")}))


if __name__ == "__main__":
    main()
