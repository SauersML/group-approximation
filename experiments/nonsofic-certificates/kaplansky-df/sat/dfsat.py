#!/usr/bin/env python3
"""SAT search for strict one-sided inverse pairs in F_2[G], G = L_{F_2}(1,2)^x.

Fix finite supports A, B of group elements. The unknowns are x_a (a in A) and
y_b (b in B), with alpha = sum x_a [a] and beta = sum y_b [b]. Put
z_ab = x_a AND y_b. Then

    alpha beta = 1   <=>  for every g in AB:  XOR_{ab = g} z_ab = [g = 1],
    beta alpha != 1  <=>  OR_g w_g,  where  w_g = XOR_{ba = g} z_ab + [g = 1].

The XORs go to CryptoMiniSat as native XOR clauses (Gauss-Jordan). UNSAT means
no strict pair has supp alpha in A and supp beta in B. Every SAT model is
recomputed in F_2[G] and written as a kaplansky-df certificate, which must then
pass certcheck.py in dual mode before anyone calls it a certificate.

Families (generators; balls are taken in generators and inverses):
  v       Thompson V: A = (0,10,11)->(00,01,1), B = (0,10,110,111)->(0,100,101,11),
          C = (0,10,11)->(11,0,10), P = (0,10,11)->(10,0,11).
  eld     the OpenAI nine-leaf triple: E_ij(r) = 1 + S[alpha_i] r T[alpha_j] on
          alpha = (000,001,01), r in {1,s0,s1,t0,t1}, and the compressors u, v.
Controls:
  leavitt-control  the same encoder on monomial bases of R itself (products are
          F_2-sums of monomials). t0 s0 = 1 != s0 t0 must be found: tests the
          strictness clause and the extraction.
  --no-strict      drops the strictness clause, so trivial units must be found.

Run on MSI only, e.g.
  python3 dfsat.py --lib <nonsofic-certificates dir> --family v --ra 2 --rb 3 --out run.json
"""

import argparse
import json
import os
import sys
import time
from collections import defaultdict


def generators(L, family):
    tu = L.thompson_unit
    if family == "v":
        A = tu(["0", "10", "11"], ["00", "01", "1"])
        B = tu(["0", "10", "110", "111"], ["0", "100", "101", "11"])
        C = tu(["0", "10", "11"], ["11", "0", "10"])
        P = tu(["0", "10", "11"], ["10", "0", "11"])
        return {"A": A, "B": B, "C": C, "P": P}
    if family == "eld":
        alpha = ["000", "001", "01"]
        beta = ["1000", "1001", "101"]
        nu = ["1100", "1101", "111"]
        zeta = ["100", "101", "11"]
        ring = {"1": L.ONE, "s0": L.s0, "s1": L.s1, "t0": L.t0, "t1": L.t1}
        gens = {}
        for i in range(3):
            for j in range(3):
                if i == j:
                    continue
                for name, r in ring.items():
                    n = L.S(alpha[i]) * r * L.T(alpha[j])
                    gens["E%d%d_%s" % (i, j, name)] = L.one_plus_nilpotent(n)
        dom = alpha + beta + nu
        gens["u"] = tu(dom, [a + "0" for a in alpha] + [a + "1" for a in alpha] + zeta)
        gens["v"] = tu(dom, [a + "0" for a in alpha] + zeta + [a + "1" for a in alpha])
        return gens
    raise ValueError("unknown family %r" % family)


def ball(L, gens, radius):
    steps = []
    for g in gens.values():
        steps.append(g)
        inv = g.inverse()
        if inv.key != g.key:
            steps.append(inv)
    seen = {L.IDENTITY.key: L.IDENTITY}
    frontier = [L.IDENTITY]
    for _ in range(radius):
        nxt = []
        for x in frontier:
            for s in steps:
                y = x * s
                if y.key not in seen:
                    seen[y.key] = y
                    nxt.append(y)
        frontier = nxt
    return list(seen.values())


def leavitt_monomials(L, depth):
    words = [""]
    for d in range(1, depth + 1):
        words += [format(i, "0%db" % d) for i in range(2 ** d)]
    out = []
    for a in words:
        for b in words:
            if a.endswith("1") and b.endswith("1"):
                continue
            out.append(L.Elem.from_terms([(a, b)]))
    return out


def build(L, A, B, group_mode):
    """Return (ab, ba, identity_key): maps product key -> list of pair indices."""
    ab = defaultdict(list)
    ba = defaultdict(list)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            pair = i * len(B) + j
            if group_mode:
                ab[(a * b).key].append(pair)
                ba[(b * a).key].append(pair)
            else:
                for term in (a * b).terms:
                    ab[term].append(pair)
                for term in (b * a).terms:
                    ba[term].append(pair)
    ident = L.IDENTITY.key if group_mode else ("", "")
    return ab, ba, ident


def encode_and_solve(A, B, ab, ba, ident, strict, time_limit):
    from pycryptosat import Solver
    s = Solver(threads=1, time_limit=time_limit)
    nA, nB = len(A), len(B)
    x = lambda i: 1 + i
    y = lambda j: 1 + nA + j
    z = lambda p: 1 + nA + nB + p
    nz = nA * nB
    for p in range(nz):
        i, j = divmod(p, nB)
        s.add_clause([-z(p), x(i)])
        s.add_clause([-z(p), y(j)])
        s.add_clause([z(p), -x(i), -y(j)])
    stats = {"vars_x": nA, "vars_y": nB, "vars_z": nz, "ab_cells": len(ab), "ba_cells": len(ba)}
    if ident not in ab:
        stats["trivial"] = "identity not in AB"
        return "UNSAT", None, stats
    forced = 0
    for key, pairs in ab.items():
        rhs = key == ident
        if len(pairs) == 1 and not rhs:
            s.add_clause([-z(pairs[0])])
            forced += 1
        else:
            s.add_xor_clause([z(p) for p in pairs], rhs)
    stats["forced_zero_pairs"] = forced
    if strict:
        w = 1 + nA + nB + nz
        ors = []
        for key, pairs in ba.items():
            s.add_xor_clause([z(p) for p in pairs] + [w], key == ident)
            ors.append(w)
            w += 1
        s.add_clause(ors)
    t0 = time.time()
    sat, sol = s.solve()
    stats["solve_seconds"] = round(time.time() - t0, 3)
    if sat is None:
        return "UNKNOWN", None, stats
    if not sat:
        return "UNSAT", None, stats
    xs = [i for i in range(nA) if sol[x(i)]]
    ys = [j for j in range(nB) if sol[y(j)]]
    return "SAT", (xs, ys), stats


def verify_group(L, GA, A, B, xs, ys):
    alpha = GA.GroupAlgebraElement([A[i] for i in xs])
    beta = GA.GroupAlgebraElement([B[j] for j in ys])
    return (alpha * beta).is_one(), (beta * alpha).is_one(), len(alpha), len(beta)


def certificate(A, B, xs, ys, note):
    units, alpha, beta = {}, [], []
    for tag, idx, src, out in (("a", xs, A, alpha), ("b", ys, B, beta)):
        for k in idx:
            name = "%s%d" % (tag, k)
            u = src[k]
            units[name] = {"val": u.val.to_json(), "inv": u.inv.to_json()}
            out.append(name)
    return {"type": "kaplansky-df", "note": note, "units": units, "alpha": alpha, "beta": beta}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True, help="directory holding leavitt.py and groupalg.py")
    ap.add_argument("--family", required=True, choices=["v", "eld", "leavitt-control"])
    ap.add_argument("--ra", type=int, default=1)
    ap.add_argument("--rb", type=int, default=1)
    ap.add_argument("--no-strict", action="store_true")
    ap.add_argument("--time-limit", type=float, default=600.0)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    L = __import__("leavitt") if args.lib in sys.path else None
    sys.path.insert(0, args.lib)
    import leavitt as L
    import groupalg as GA
    L.set_dual(False)
    t0 = time.time()
    report = {"family": args.family, "ra": args.ra, "rb": args.rb, "strict": not args.no_strict}
    if args.family == "leavitt-control":
        A = leavitt_monomials(L, args.ra)
        B = leavitt_monomials(L, args.rb)
        group_mode = False
    else:
        gens = generators(L, args.family)
        report["generators"] = sorted(gens)
        A = ball(L, gens, args.ra)
        B = A if args.rb == args.ra else ball(L, gens, args.rb)
        group_mode = True
    ab, ba, ident = build(L, A, B, group_mode)
    report["build_seconds"] = round(time.time() - t0, 3)
    status, model, stats = encode_and_solve(A, B, ab, ba, ident, not args.no_strict, args.time_limit)
    report.update(stats)
    report["status"] = status
    if model is not None:
        xs, ys = model
        report["supp_alpha"], report["supp_beta"] = len(xs), len(ys)
        if group_mode:
            ab_one, ba_one, la, lb = verify_group(L, GA, A, B, xs, ys)
            report["recheck"] = {"alpha_beta_is_one": ab_one, "beta_alpha_is_one": ba_one,
                                 "supp_alpha": la, "supp_beta": lb}
            if ab_one and not ba_one:
                cert = certificate(A, B, xs, ys, "dfsat family=%s ra=%d rb=%d" % (args.family, args.ra, args.rb))
                path = os.path.splitext(args.out)[0] + ".cert.json"
                with open(path, "w") as fh:
                    json.dump(cert, fh)
                report["certificate"] = path
        else:
            report["model"] = {"alpha": [L.render(A[i]) for i in xs], "beta": [L.render(B[j]) for j in ys]}
    report["total_seconds"] = round(time.time() - t0, 3)
    with open(args.out, "w") as fh:
        json.dump(report, fh, indent=1)
    print(json.dumps({k: v for k, v in report.items() if k != "model"}))


if __name__ == "__main__":
    main()
