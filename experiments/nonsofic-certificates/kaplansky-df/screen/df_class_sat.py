#!/usr/bin/env python3
"""SAT search for strict one-sided inverse pairs on a screened window, using the screen's classes as XOR rows.

Let (A, B) be a window screened by df_table_screen.py --verify. Every finite image found merges
cells of BA u {1} only within the surviving classes. By
research/one-sided-inverse-pairs-transfer-to-table-realizations.md (Corollary 1), the defect
beta alpha - 1 has coefficient 0 at every singleton cell and coefficient sum 0 on every class.
Each singleton cell therefore gives the XOR row "coefficient of beta alpha at g = [g = 1]", and the
strictness clause ranges over class cells only. The other rows are those of dfsat.py: the rows for
alpha beta = 1, odd supports, and supports that leave the degree-zero units and the listed finite
subgroups.

UNSAT means no strict pair has supp alpha in A and supp beta in B. It is a CryptoMiniSat verdict
without a proof log, and so is recorded under Attempts only. A SAT model is rechecked in F_2[G].

MSI (kdf-sat venv, which has pycryptosat):
  python df_class_sat.py --final runs/r2.final.json --window v:2:2 --out runs/sat-v-2-2.json
"""
import argparse
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import df_table_screen as T  # noqa: E402  (also puts the Leavitt library and ../sat on sys.path)
import dfsat  # noqa: E402

L = T.L


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--final", required=True)
    ap.add_argument("--window", required=True)
    ap.add_argument("--time-limit", type=float, default=1800.0)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    fam, ra, rb = args.window.split(":")
    ra, rb = int(ra), int(rb)
    rec = next(r for r in json.load(open(args.final)) if (r["family"], r["ra"], r["rb"]) == (fam, ra, rb))
    report = {"family": fam, "ra": ra, "rb": rb, "screen_status": rec["status"],
              "classes": rec["final_classes"]}
    t0 = time.time()
    nA, nB, cells, rels, ba_cells = T.table(fam, ra, rb)
    gens = T.family_gens(fam)
    A = dfsat.ball(L, gens, ra)
    B = A if ra == rb else dfsat.ball(L, gens, rb)
    ab, ba, ident = dfsat.build(L, A, B, True)
    in_class = {cells[k].key: ci for ci, cl in enumerate(rec["final_classes_cells"]) for k in cl}
    assert set(in_class) <= set(ba), "class cells must lie in BA u {1}"
    prune_x, prune_or, report["prune"] = dfsat.prune_rows(L, A, B, gens, fam)
    report["build_seconds"] = round(time.time() - t0, 3)
    if not in_class:
        report.update(status="UNSAT", reason="screen dead: no class survives")
    elif any(not idx for side, idx in prune_or):
        report.update(status="UNSAT", reason="a support is forced inside a directly finite subgroup")
    else:
        from pycryptosat import Solver
        s = Solver(threads=1, time_limit=args.time_limit)
        x = lambda i: 1 + i
        y = lambda j: 1 + nA + j
        z = lambda p: 1 + nA + nB + p
        nz = nA * nB
        for side, idx, rhs in prune_x:
            s.add_xor_clause([(x if side == "x" else y)(k) for k in idx], rhs)
        for side, idx in prune_or:
            s.add_clause([(x if side == "x" else y)(k) for k in idx])
        for p in range(nz):
            i, j = divmod(p, nB)
            s.add_clause([-z(p), x(i)])
            s.add_clause([-z(p), y(j)])
            s.add_clause([z(p), -x(i), -y(j)])
        for key, pairs in ab.items():
            s.add_xor_clause([z(p) for p in pairs], key == ident)
        w, cls = 1 + nA + nB + nz, {}
        singleton_rows = 0
        for key, pairs in ba.items():
            if key in in_class:
                s.add_xor_clause([z(p) for p in pairs] + [w], key == ident)
                cls.setdefault(in_class[key], []).append(w)
                w += 1
            else:
                s.add_xor_clause([z(p) for p in pairs], key == ident)
                singleton_rows += 1
        for ws in cls.values():
            s.add_xor_clause(ws, False)
        s.add_clause([v for ws in cls.values() for v in ws])
        report.update(vars_z=nz, singleton_rows=singleton_rows, class_cells=len(in_class))
        t1 = time.time()
        sat, sol = s.solve()
        report["solve_seconds"] = round(time.time() - t1, 3)
        if sat is None:
            report["status"] = "UNKNOWN"
        elif not sat:
            report["status"] = "UNSAT"
        else:
            import groupalg as GA
            xs = [i for i in range(nA) if sol[x(i)]]
            ys = [j for j in range(nB) if sol[y(j)]]
            ab_one, ba_one, la, lb = dfsat.verify_group(L, GA, A, B, xs, ys)
            report.update(status="SAT", recheck={"alpha_beta_is_one": ab_one, "beta_alpha_is_one": ba_one,
                                                 "supp_alpha": la, "supp_beta": lb})
            if ab_one and not ba_one:
                path = os.path.splitext(args.out)[0] + ".cert.json"
                json.dump(dfsat.certificate(A, B, xs, ys, "df_class_sat %s" % args.window), open(path, "w"))
                report["certificate"] = path
    report["total_seconds"] = round(time.time() - t0, 3)
    json.dump(report, open(args.out, "w"), indent=1)
    print(json.dumps(report))


if __name__ == "__main__":
    main()
