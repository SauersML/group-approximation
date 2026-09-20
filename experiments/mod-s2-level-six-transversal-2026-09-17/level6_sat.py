#!/usr/bin/env python3
"""Transversal search in W_Q with exact solvers (independent of the HiGHS MILP).

Input: the pickle written by level6_modp.py ({"Phi", "block", ...}).
  mode xor2   : CryptoMiniSat, x in {0,1}^m, exactly one per block, and the
                98 (or 108) parity constraints x . Phi_2[:, k] = 0 mod 2.
  mode cpsat  : OR-tools CP-SAT, the same with x . Phi_p[:, k] = p z_k for
                every p in PRIMES (small primes; comma separated).
A solution is re-checked in exact integer arithmetic against every prime in
the pickle, including the two 31-bit primes.

Usage: python3 level6_sat.py phi.pkl xor2|cpsat [PRIMES] [SECONDS]
"""
import pickle
import sys
import time


def exactly_one_cnf(vs):
    cl = [list(vs)]
    for i in range(len(vs)):
        for j in range(i + 1, len(vs)):
            cl.append([-vs[i], -vs[j]])
    return cl


def check(T, Phi, block):
    ok = sorted(block[j] for j in T) == sorted(set(block))
    return ok, {p: all(sum(Phi[p][j][k] for j in T) % p == 0
                       for k in range(len(Phi[p][0]))) for p in Phi}


def indep_columns_mod2(Phi2):
    """Independent parity checks: a basis of the column space of Phi_2."""
    m, r = len(Phi2), len(Phi2[0])
    cols = [sum(((Phi2[c][k] & 1) << c) for c in range(m)) for k in range(r)]
    basis, piv = [], []
    for v in cols:
        for b, pb in zip(basis, piv):
            if (v >> pb) & 1:
                v ^= b
        if v:
            pb = v.bit_length() - 1
            for i in range(len(basis)):
                if (basis[i] >> pb) & 1:
                    basis[i] ^= v
            basis.append(v)
            piv.append(pb)
    return basis


def run_xor2(Phi, block, seconds):
    from pycryptosat import Solver
    m = len(block)
    s = Solver(threads=4, time_limit=seconds)
    for b in sorted(set(block)):
        for cl in exactly_one_cnf([c + 1 for c in range(m) if block[c] == b]):
            s.add_clause(cl)
    basis = indep_columns_mod2(Phi[2])
    for v in basis:
        s.add_xor_clause([c + 1 for c in range(m) if (v >> c) & 1], False)
    print(f"xor2: {len(basis)} independent parity checks", flush=True)
    sat, sol = s.solve()
    if sat is None:
        return "UNKNOWN", None
    if not sat:
        return "UNSAT", None
    return "SAT", [c for c in range(m) if sol[c + 1]]


def run_cpsat(Phi, block, primes, seconds):
    from ortools.sat.python import cp_model
    m = len(block)
    md = cp_model.CpModel()
    x = [md.NewBoolVar(f"x{c}") for c in range(m)]
    for b in sorted(set(block)):
        md.AddExactlyOne([x[c] for c in range(m) if block[c] == b])
    nb = len(set(block))
    for p in primes:
        for k in range(len(Phi[p][0])):
            col = [(c, Phi[p][c][k] % p) for c in range(m) if Phi[p][c][k] % p]
            if not col:
                continue
            z = md.NewIntVar(0, nb * (p - 1) // p + 1, f"z{p}_{k}")
            md.Add(sum(a * x[c] for c, a in col) == p * z)
    sv = cp_model.CpSolver()
    sv.parameters.max_time_in_seconds = seconds
    sv.parameters.num_workers = 4
    st = sv.Solve(md)
    name = sv.StatusName(st)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return name, [c for c in range(m) if sv.Value(x[c])]
    return name, None


def main(pkl, mode, primes="2,3,5,7,11,13", seconds="3600"):
    d = pickle.load(open(pkl, "rb"))
    Phi, block = d["Phi"], d["block"]
    t0 = time.time()
    if mode == "xor2":
        st, T = run_xor2(Phi, block, float(seconds))
    else:
        st, T = run_cpsat(Phi, block, [int(p) for p in primes.split(",")],
                          float(seconds))
    print(mode, primes if mode != "xor2" else "2", "status", st, "solution", T,
          f"[{time.time()-t0:.0f}s]", flush=True)
    if T is not None:
        print("exact re-check (blocks ok, per prime):", check(T, Phi, block))


if __name__ == "__main__":
    main(*sys.argv[1:])
