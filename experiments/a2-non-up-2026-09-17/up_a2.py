#!/usr/bin/env python3
"""SAT search for pairs of finite sets WITHOUT a unique product in vertex-regular Ã2 lattices.

Host.  (lambda, T) a triangle presentation over PG(2,q) (Cartwright--Mantero--Steger--Zappa),
Gamma_T = < a_x | a_x a_y a_z = 1, (x,y,z) in T >, acting simply transitively on the vertices of an
Ã2 building.  Gamma_0 = ker(Gamma_T -> Z/3, a_x -> 1) is torsion-free of index 3 with property (T).
Exact multiplication: the confluent length-2 rewriting system of a2group.py (copied from lane sw-108,
experiments/a2-left-orderability-2026-09-17); confluence, relators and sphere sizes are re-checked here
before every run.

Question.  Finite A, B with 1 in A, 1 in B, A in B(ra), B in B(rb) (word metric of Gamma_T in the
letters a_x^{+-1}), A, B inside the host H (Gamma_0, or Gamma_T when T has no (x,x,x) triple), such
that every product ab is represented at least twice.

Why.  If alpha beta = 0 in k[H] with alpha, beta nonzero, then (supp alpha, supp beta) has no uniquely
represented product, over EVERY field k.  Translating (alpha -> a0^-1 alpha, beta -> beta b0^-1) puts 1
in both supports.  So UNSAT excludes zero divisors over every field with rad_L(supp alpha) <= ra and
rad_R(supp beta) <= rb; SAT shows H lacks unique products.

Encoding as in experiments/zero-divisor-tf/up_sat.py: z_p <-> x_a & y_b; each product cell has count
0 or >= 2 (direct clauses for cells of size <= 10, a sequential counter above).  Every SAT model is
re-verified by exact recomputation.

Control (--control): the full Gamma_T of a presentation with a triple (x,x,x) has a_x^3 = 1, so
{1, a_x, a_x^-1} is a pair without unique products at radius 1: the solver must answer SAT.

Usage:  up_a2.py --file presentations_q3.json --index 0 --host gamma0 --ra 2 --rb 2 --out runs/x.jsonl
"""

import argparse
import json
import os
import time
from collections import defaultdict

from a2group import A2Group


def typ(w):
    return sum(e for (_, e) in w) % 3


def expected_spheres(q, R):
    """Vertices of shape (m,n): N(m,0) = N(0,m) = (q^2+q+1) q^(2(m-1)),
    N(m,n) = (q^2+q+1) q^(2(m-1)) * (q^2+q) q^(2(n-1)) for m, n >= 1."""
    c1, c2 = q * q + q + 1, q * q + q
    out = [1]
    for r in range(1, R + 1):
        s = 2 * c1 * q ** (2 * (r - 1))
        for m in range(1, r):
            n = r - m
            s += c1 * q ** (2 * (m - 1)) * c2 * q ** (2 * (n - 1))
        out.append(s)
    return out


def host_ball(G, r, host):
    layers = G.ball(r)
    elems = [w for l in layers for w in l]
    if host == "gamma0":
        elems = [w for w in elems if typ(w) == 0]
    assert elems[0] == ()
    return elems, [len(l) for l in layers]


def verify(G, Asel, Bsel):
    if not Asel or not Bsel:
        return False, "empty"
    cnt = defaultdict(int)
    for a in Asel:
        for b in Bsel:
            cnt[G.mul(a, b)] += 1
    ones = sum(1 for v in cnt.values() if v == 1)
    return ones == 0, ("ok" if ones == 0 else "%d uniquely represented products" % ones)


def build(G, A, B):
    from pysat.formula import CNF
    nA, nB = len(A), len(B)
    cells = defaultdict(list)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            cells[G.mul(a, b)].append((i, j))
    cnf = CNF()
    top = [nA + nB]

    def new():
        top[0] += 1
        return top[0]

    x = lambda i: 1 + i
    y = lambda j: 1 + nA + j
    cnf.append([x(0)])
    cnf.append([y(0)])
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
            s_prev = d_prev = None
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


def word(w):
    return "".join(("a%d" % x) if e == 1 else ("A%d" % x) for (x, e) in w) or "1"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", required=True)
    ap.add_argument("--index", type=int, nargs="+", required=True)
    ap.add_argument("--host", choices=["gamma0", "full"], default="gamma0")
    ap.add_argument("--ra", type=int, required=True)
    ap.add_argument("--rb", type=int, required=True)
    ap.add_argument("--control", action="store_true")
    ap.add_argument("--solver", default="cadical153")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    from pysat.solvers import Solver
    Ts = json.load(open(args.file))
    for idx in args.index:
        t0 = time.time()
        T = [tuple(t) for t in Ts[idx]]
        G = A2Group(T)
        q = round(len(G.N[0])) - 1
        ok, npairs = G.check_confluence()
        assert ok, "rewriting system not confluent"
        assert G.check_relators()
        torsion_triples = sum(1 for t in T if len(set(t)) == 1)
        if args.host == "full" and torsion_triples and not args.control:
            raise SystemExit("T%d has (x,x,x) triples: Gamma_T has torsion; use --host gamma0" % idx)
        R = max(args.ra, args.rb)
        A, spheres = host_ball(G, args.ra, args.host)
        B, spheres_b = host_ball(G, args.rb, args.host)
        sp = spheres if len(spheres) >= len(spheres_b) else spheres_b
        assert sp == expected_spheres(q, R), (sp, expected_spheres(q, R))
        rep = {"file": os.path.basename(args.file), "index": idx, "q": q, "host": args.host,
               "control": args.control, "torsion_triples": torsion_triples,
               "confluent_critical_pairs": npairs, "spheres_checked": sp,
               "ra": args.ra, "rb": args.rb, "size_A": len(A), "size_B": len(B),
               "pairs": len(A) * len(B)}
        cnf, stats = build(G, A, B)
        rep.update(stats)
        rep.update({"vars": cnf.nv, "clauses": len(cnf.clauses), "build_seconds": round(time.time() - t0, 2)})
        t1 = time.time()
        with Solver(name=args.solver, bootstrap_with=cnf.clauses) as S:
            res = S.solve()
            rep["solve_seconds"] = round(time.time() - t1, 2)
            rep["solver"] = args.solver
            if res:
                model = set(v for v in S.get_model() if v > 0)
                Asel = [A[i] for i in range(len(A)) if 1 + i in model]
                Bsel = [B[j] for j in range(len(B)) if 1 + len(A) + j in model]
                okv, msg = verify(G, Asel, Bsel)
                rep.update({"result": "SAT", "verified": okv, "verify_message": msg,
                            "A": [word(a) for a in Asel], "B": [word(b) for b in Bsel]})
            else:
                rep["result"] = "UNSAT"
        with open(args.out, "a") as f:
            f.write(json.dumps(rep) + "\n")
        print(json.dumps({k: v for k, v in rep.items() if k not in ("A", "B")}), flush=True)


if __name__ == "__main__":
    main()
