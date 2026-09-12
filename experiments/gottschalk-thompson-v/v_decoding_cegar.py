"""Rule-level test of invariant-output windows over Thompson's group V.

Lane `gottschalk-thompson-v`, 2026-09-12. The rule-free screen (v_window_screen.py)
is blind above the radius of
research/large-window-table-groups-present-the-ambient-group.md, so here windows are
tested at the level of local rules.

**Rules.** f = sum_j c_j mu_j over F_2 on the memory M. The mu_j run over the
<h>-orbit sums of the monomials of degree 1..D in the coordinates m in M, where <h>
acts by m -> h m. So f is <h>-invariant, and tau(x)(g) = f(x(g m))_m has output
constant on right cosets of <h>.

**Decoding at 1.** Suppose x(1) is determined by (tau(x)(s))_(s in S) for every x on
the cells SM. Then:
- sigma(y)(g) = d(y(g s))_s is a left inverse with memory S, so tau is injective;
- every pattern on {1, h} with distinct symbols is a Garden of Eden
  (invariant-output-injective-automata-need-invisible-symmetry).
That is a strict pair over V.

**CEGAR.**
- A: find coefficients c that separate every stored counterexample (x, y), i.e.
  OR_s XOR_j c_j [mu_j(x|sM) + mu_j(y|sM)] = 1, and that satisfy f(0...0) != f(1...1).
- B: for the current c, look for x, y on SM with x(1) = 0, y(1) = 1 and equal outputs
  on S.
  - UNSAT -> DECODER, with c as the certificate candidate.
  - SAT -> the pair becomes a new counterexample for A.
- A UNSAT -> NO_RULE: no invariant rule of degree <= D decodes x(1) from S on this
  window.

**Controls.**
- A window excluded by a finite image of its table group
  (strict-pairs-transfer-to-table-realizations) must return NO_RULE for every D.
- For h an involution, D = 1 must return NO_RULE
  (linear-invariant-output-automata-fail-augmentation).
A DECODER in either case is a bug.

MSI usage (python-sat):
  python3 v_decoding_cegar.py --family gl32-leaves-f-order2 --radii 1:1 --degree 2 --out r.json
"""

import argparse
import itertools
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import v_window_screen as vs  # noqa: E402
from pysat.solvers import Solver  # noqa: E402


class Pool:
    def __init__(self, start=0):
        self.n = start

    def new(self):
        self.n += 1
        return self.n


def and_var(pool, clauses, lits):
    if len(lits) == 1:
        return lits[0]
    a = pool.new()
    for lit in lits:
        clauses.append([-a, lit])
    clauses.append([a] + [-lit for lit in lits])
    return a


def xor_var(pool, clauses, lits):
    """A literal equal to the XOR of lits, or None for the empty XOR (constant 0)."""
    if not lits:
        return None
    t = lits[0]
    for lit in lits[1:]:
        u = pool.new()
        clauses.extend([[-u, t, lit], [-u, -t, -lit], [u, -t, lit], [u, t, -lit]])
        t = u
    return t


def build_window(E, family, r_m, r_s, degree):
    gens, h_name = vs.FAMILIES[family]
    h, order, powers, S, M = vs.window(E, gens, h_name, r_m, r_s)
    Mkeys = sorted(M, key=repr)
    Skeys = sorted(S, key=repr)
    midx = {k: i for i, k in enumerate(Mkeys)}
    hperm = [midx[(h * M[k]).key] for k in Mkeys]
    orbits, seen = [], set()
    for d in range(1, degree + 1):
        for T in itertools.combinations(range(len(Mkeys)), d):
            T = frozenset(T)
            if T in seen:
                continue
            orb, U = [], T
            while U not in seen:
                orb.append(U)
                seen.add(U)
                U = frozenset(hperm[i] for i in U)
            orbits.append(orb)
    cell, table = {}, []
    for sk in Skeys:
        row = []
        for mk in Mkeys:
            key = (S[sk] * M[mk]).key
            if key not in cell:
                cell[key] = len(cell)
            row.append(cell[key])
        table.append(row)
    return {"order": order, "S": len(Skeys), "M": len(Mkeys), "orbits": orbits, "table": table,
            "ncells": len(cell), "one": cell[vs.IDENTITY.key]}


def monomial_value(z, row, T):
    return all(z[row[i]] for i in T)


def orbit_diff(x, y, row, orb):
    v = False
    for T in orb:
        v ^= monomial_value(x, row, T) ^ monomial_value(y, row, T)
    return v


def build_verifier(W, J, solver_name):
    """B with coefficient variables 1..J passed as assumptions."""
    pool = Pool(J)
    xv = [pool.new() for _ in range(W["ncells"])]
    yv = [pool.new() for _ in range(W["ncells"])]
    clauses = [[-xv[W["one"]]], [yv[W["one"]]]]
    cache = {}

    def mono(vars_, cells, tag):
        key = (tag, cells)
        if key not in cache:
            cache[key] = and_var(pool, clauses, [vars_[c] for c in cells])
        return cache[key]
    for row in W["table"]:
        gated = []
        for j, orb in enumerate(W["orbits"]):
            lits = []
            for T in orb:
                cells = tuple(sorted({row[i] for i in T}))
                lits.append(mono(xv, cells, "x"))
                lits.append(mono(yv, cells, "y"))
            d = xor_var(pool, clauses, lits)
            if d is not None:
                gated.append(and_var(pool, clauses, [j + 1, d]))
        t = xor_var(pool, clauses, gated)
        if t is not None:
            clauses.append([-t])
    solver = Solver(name=solver_name, bootstrap_with=clauses)
    return solver, xv, yv, len(clauses), pool.n


def cegar(W, solver_name, max_iter, time_limit):
    J = len(W["orbits"])
    t0 = time.time()
    A = Solver(name=solver_name)
    apool = Pool(J)
    aclauses = []
    odd = [j + 1 for j, orb in enumerate(W["orbits"]) if len(orb) % 2 == 1]
    t = xor_var(apool, aclauses, odd)
    if t is None:
        return {"outcome": "NO_RULE", "reason": "every orbit even: f(0) = f(1) forced", "iterations": 0}
    aclauses.append([t])
    for cl in aclauses:
        A.add_clause(cl)
    B, xv, yv, nclauses, nvars = build_verifier(W, J, solver_name)
    info = {"orbits": J, "verifier_clauses": nclauses, "verifier_vars": nvars}
    for it in range(1, max_iter + 1):
        if time.time() - t0 > time_limit:
            return dict(info, outcome="TIME_LIMIT", iterations=it - 1)
        if not A.solve():
            return dict(info, outcome="NO_RULE", iterations=it - 1)
        model = set(lit for lit in A.get_model() if lit > 0)
        c = [(j + 1) in model for j in range(J)]
        assumptions = [(j + 1) if c[j] else -(j + 1) for j in range(J)]
        if not B.solve(assumptions=assumptions):
            return dict(info, outcome="DECODER", iterations=it,
                        coefficients=[j for j in range(J) if c[j]])
        mb = set(lit for lit in B.get_model() if lit > 0)
        x = [xv[i] in mb for i in range(W["ncells"])]
        y = [yv[i] in mb for i in range(W["ncells"])]
        cl, sep = [], []
        for row in W["table"]:
            Js = [j + 1 for j, orb in enumerate(W["orbits"]) if orbit_diff(x, y, row, orb)]
            p = xor_var(apool, cl, Js)
            if p is not None:
                sep.append(p)
        if not sep:
            return dict(info, outcome="NO_RULE", iterations=it, reason="counterexample no rule separates")
        for clause in cl + [sep]:
            A.add_clause(clause)
        if it % 50 == 0:
            print("  iteration %d, %.0fs" % (it, time.time() - t0), flush=True)
    return dict(info, outcome="ITERATION_LIMIT", iterations=max_iter)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--family", required=True)
    ap.add_argument("--radii", default="1:1")
    ap.add_argument("--degree", type=int, default=2)
    ap.add_argument("--solver", default="cadical153")
    ap.add_argument("--max-iter", type=int, default=5000)
    ap.add_argument("--time-limit", type=float, default=3000)
    ap.add_argument("--out")
    args = ap.parse_args()
    E = vs.named_elements()
    results = []
    for rr in args.radii.split(","):
        r_m, r_s = (int(v) for v in rr.split(":"))
        t0 = time.time()
        W = build_window(E, args.family, r_m, r_s, args.degree)
        rec = {"family": args.family, "r_m": r_m, "r_s": r_s, "degree": args.degree,
               "order": W["order"], "S": W["S"], "M": W["M"], "cells": W["ncells"]}
        rec.update(cegar(W, args.solver, args.max_iter, args.time_limit))
        rec["seconds"] = round(time.time() - t0, 1)
        print(json.dumps({k: v for k, v in rec.items() if k != "coefficients"}), flush=True)
        results.append(rec)
        if args.out:
            json.dump(results, open(args.out, "w"))
    print("CEGAR_DONE")


if __name__ == "__main__":
    main()
