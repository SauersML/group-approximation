#!/usr/bin/env python3
"""Bilinear screens for left-invertible lifts of s0 in S_- = eps_- F_3[L_{F_3}(1,2)^x].

Lane gk3-ternary-bilinear. The linear screens of pscreen.py fix one lift alpha of s0. Here alpha
ranges over a whole affine space

    alpha = alpha0 + sum_i lambda_i k_i,    lambda in F_3^d,

where alpha0 is the explicit support-four lift of s0 and k_1..k_d is a basis of ker(pi) inside the
span of a lift ball. The unknowns are lambda, beta in span(C) and n in span{[p] - 1 : p in P}, P the
level-two unitriangular 3-group, with

    beta alpha = 1 + n.                                              (*)

(*) is bilinear in (lambda, beta). Any solution gives a left inverse (1 + n)^(-1) beta of a lift of
s0, so S_- is not directly finite (condition (V3*)).

Mode exhaust: every lambda with index in [lo, hi) of the base-3 enumeration; each slice is the
linear screen of pscreen.py, and every UNSAT slice keeps a dual functional that is re-verified from
a fresh unit registry.

Mode relax: put nu_(c,i) = beta_c lambda_i. (*) becomes linear in (beta, nu, n):
sum_c beta_c [c] alpha0 + sum_(c,i) nu_(c,i) [c] k_i - n = 1. If this relaxation is UNSAT, one dual
functional phi (killing [c] alpha0, [c] k_i and [p] - 1, with phi(1) != 0) excludes every lambda
at once. If it is SAT, the relaxation says nothing.

Controls (must pass before any instance runs):
  K1 planted: alpha0 = [g] + k with direction -k; exhaust finds lambda = 1 SAT, relax is SAT.
  K2 forced UNSAT: alpha0 = e_- with kernel directions; pi(alpha) is an idempotent != 1 of R, which
     has no left inverse, so every slice and the relaxation must be UNSAT with verified certificates.
Run on MSI only.
"""

import argparse
import itertools
import json
import random
import sys
import time

import tleavitt as L
import pscreen as PS


def kernel_basis(Sm, keys):
    """A basis of ker(pi) inside span{[g] : g in keys}, as dicts over basis keys."""
    el, out = PS.Eliminator(), []
    for j, k in enumerate(keys):
        col = Sm.units[k].val
        rem, coeffs = el._reduce(dict(col), {})
        if rem:
            el.insert(j, col)
        else:
            vec = {}
            for i, c in L.add({j: 1}, coeffs, -1).items():
                vec = L.add(vec, {keys[i]: c})
            if vec:
                out.append(vec)
    for vec in out:
        assert not Sm.evaluate(vec), "kernel vector does not evaluate to zero"
    return out


def lam_of_index(idx, d):
    lam = []
    for _ in range(d):
        lam.append(idx % 3)
        idx //= 3
    return lam


def alpha_of(alpha0, dirs, lam):
    a = dict(alpha0)
    for li, k in zip(lam, dirs):
        if li:
            a = L.add(a, k, li)
    return a


def relaxation(Sm, alpha0, dirs, C, P):
    """Linearized (*): returns (sat, stats, phi)."""
    one = Sm.one()
    cols = {}
    for c in C:
        cols[("c", c)] = Sm.mul({c: 1}, alpha0)
        for i, k in enumerate(dirs):
            cols[("nu", c, i)] = Sm.mul({c: 1}, k)
    for p in P:
        pk = Sm.of_unit(p)
        if pk != one:
            cols[("p", L.key(p.val))] = L.add(pk, one, -1)
    el = PS.Eliminator()
    names = list(cols)
    rows = set()
    for j, name in enumerate(names):
        el.insert(j, cols[name])
        rows.update(cols[name])
    stats = {"columns": len(names), "rows": len(rows), "rank": len(el.piv)}
    sol = el.solve(one)
    if sol is not None:
        return True, stats, None
    return False, stats, el.dual_certificate(one)


def verify_relaxation_certificate(units, alpha0, dirs, P, phi):
    """Recompute every relaxation column from a fresh registry; phi must kill them, phi(1) != 0."""
    Sm2 = L.SMinus()
    one = Sm2.one()
    (k1, _), = one.items()
    if phi.get(k1, 0) % 3 == 0:
        return False, "phi(1) = 0"

    def rebuild(x):
        y = {}
        for k, c in x.items():
            y = L.add(y, Sm2.of_unit(units[k], c))
        return y

    a0 = rebuild(alpha0)
    ks = [rebuild(k) for k in dirs]
    for c, u in units.items():
        if c not in C_KEYS:
            continue
        cu = Sm2.of_unit(u)
        for x in [a0] + ks:
            col = Sm2.mul(cu, x)
            if sum(v * phi.get(kk, 0) for kk, v in col.items()) % 3:
                return False, "phi does not kill a product column"
    for p in P:
        col = L.add(Sm2.of_unit(p), one, -1)
        if sum(v * phi.get(kk, 0) for kk, v in col.items()) % 3:
            return False, "phi does not kill a correction column"
    return True, "ok"


C_KEYS = set()


def multiplier_group(name):
    """Finite subgroups K <= G used to absorb units of eps_- F_3[K] lying over 1 into the beta support.

    If u is a unit of eps_- F_3[K] with pi(u) = 1 and beta alpha = u, then (u^-1 beta) alpha = 1 and
    u^-1 beta lies in span(K . C). So screening span(K . C) covers every such correction at once.
    """
    if name == "none":
        return [L.IDENTITY]
    if name == "klein":
        h1 =L.diagonal_unit(["00", "01", "10", "11"], [1, 1, 2, 2])
        h2 = L.diagonal_unit(["00", "01", "10", "11"], [2, 2, 1, 2])
        gens = [h1, h2]
    elif name == "e2":
        gens = [L.diagonal_unit(["00", "01", "10", "11"], [2 if i == j else 1 for j in range(4)])
                for i in range(4)]
    elif name == "gl2":
        gens = [L.W, L.D, L.one_plus_nilpotent(L.mul(L.s0, L.t1)),
                L.diagonal_unit(["0", "1"], [2, 1])]
    else:
        raise ValueError(name)
    group = {L.key(L.ONE): L.IDENTITY}
    frontier = [L.IDENTITY]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = x * g
                k = L.key(y.val)
                if k not in group:
                    group[k] = y
                    nxt.append(y)
        frontier = nxt
        if len(group) > 5000:
            raise ValueError("multiplier group too large")
    return list(group.values())


def multiply_support(Sm, K, C):
    """Basis keys of K . C in S_- (signs dropped: span is what matters)."""
    out = {}
    for u in K:
        for c in C:
            k = Sm.basis(u * Sm.units[c])[0]
            out[k] = True
    return list(out)


def exhaust(Sm, alpha0, dirs, C, P, lo, hi, rng, report, tag):
    d = len(dirs)
    units_C = {k: Sm.units[k] for k in C}
    counts = {"sat": 0, "unsat_verified": 0, "unsat_unverified": 0}
    sats = []
    for idx in range(lo, min(hi, 3 ** d)):
        lam = lam_of_index(idx, d)
        alpha = alpha_of(alpha0, dirs, lam)
        sol = PS.left_inverse_screen(Sm, alpha, C, P)
        phi = PS.LAST_STATS.pop("phi", None)
        if sol is not None:
            counts["sat"] += 1
            sats.append({"index": idx, "lambda": lam,
                         "alpha": [[list(map(list, k)), c] for k, c in alpha.items()],
                         "solution": [[n[0], list(map(list, n[1])), c] for n, c in sol.items()]})
            continue
        ok, why = PS.verify_dual_certificate(units_C, alpha, P, phi or {}, alpha_units=Sm.units)
        counts["unsat_verified" if ok else "unsat_unverified"] += 1
        if not ok:
            report.setdefault("unverified", []).append({"index": idx, "why": why})
    report[tag] = {"d": d, "lo": lo, "hi": min(hi, 3 ** d), "counts": counts, "sat_instances": sats[:20]}
    return counts, sats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--family", default="mix2")
    ap.add_argument("--lift-radius", type=int, default=2)
    ap.add_argument("--radius", type=int, default=3)
    ap.add_argument("--level", type=int, default=2)
    ap.add_argument("--mode", choices=["controls", "exhaust", "relax"], required=True)
    ap.add_argument("--lo", type=int, default=0)
    ap.add_argument("--hi", type=int, default=10 ** 9)
    ap.add_argument("--max-d", type=int, default=12)
    ap.add_argument("--mult", choices=["none", "klein", "e2", "gl2"], default="none")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    rng = random.Random(20260914)
    t0 = time.time()
    Sm = L.SMinus()
    report = {"args": vars(args), "controls": {}}
    P = PS.unitriangular(args.level)
    gens = PS.family(args.family)

    # K1 planted SAT: alpha0 = [g] + k, direction -k, C a symmetric ball containing g^-1, P trivial.
    B1 = PS.ball(Sm, gens, 1)
    Klift = kernel_basis(Sm, PS.ball(Sm, gens, 2))
    g = B1[1]
    k = Klift[0]
    a0 = L.add({g: 1}, k)
    global C_KEYS
    C_KEYS = set(B1)
    c1, s1 = exhaust(Sm, a0, [L.scale(k, 2)], B1, P[:1], 0, 3, rng, report, "K1_exhaust")
    report["controls"]["K1_planted_lambda1_sat"] = any(s["index"] == 1 for s in s1)
    sat_r, _, _ = relaxation(Sm, a0, [L.scale(k, 2)], B1, P[:1])
    report["controls"]["K1_relaxation_sat"] = sat_r

    # K2 forced UNSAT: alpha0 = e_-, three kernel directions, C = mix2-type ball of radius 2.
    e_minus = L.scale(L.add(Sm.one(), Sm.of_unit(L.W)), 2)
    B2 = PS.ball(Sm, PS.family("vwd"), 2)
    C_KEYS = set(B2)
    dirs2 = Klift[:3]
    c2, s2 = exhaust(Sm, e_minus, dirs2, B2, P, 0, 27, rng, report, "K2_exhaust")
    report["controls"]["K2_every_slice_unsat_verified"] = (c2["sat"] == 0 and c2["unsat_unverified"] == 0
                                                          and c2["unsat_verified"] == 27)
    sat2, st2, phi2 = relaxation(Sm, e_minus, dirs2, B2, P)
    ok2, why2 = (verify_relaxation_certificate(Sm.units, e_minus, dirs2, P, phi2)
                 if phi2 else (False, "no phi"))
    report["controls"]["K2_relaxation_unsat_verified"] = (not sat2) and ok2
    report["K2_relaxation_stats"] = st2
    print("controls", report["controls"], "%.1fs" % (time.time() - t0), flush=True)
    if not all(report["controls"].values()) or args.mode == "controls":
        json.dump(report, open(args.out, "w"), indent=1)
        sys.exit(0 if all(report["controls"].values()) else 2)

    lift_keys = PS.ball(Sm, gens, args.lift_radius)
    C = PS.ball(Sm, gens, args.radius)
    K = multiplier_group(args.mult)
    if args.mult != "none":
        C = multiply_support(Sm, K, C)
    C_KEYS = set(C)
    alpha0 = PS.explicit_s0_lift(Sm)
    dirs = kernel_basis(Sm, lift_keys)
    report["sizes"] = {"lift_ball": len(lift_keys), "C": len(C), "P": len(P), "d": len(dirs),
                       "mult": args.mult, "K": len(K),
                       "image_feasible_alpha0": PS.image_feasible(Sm, alpha0, C, P)}
    print("sizes", report["sizes"], flush=True)
    if args.mode == "relax":
        t1 = time.time()
        sat, st, phi = relaxation(Sm, alpha0, dirs, C, P)
        rel = {"sat": sat, "stats": st, "seconds": round(time.time() - t1, 1)}
        if phi is not None:
            ok, why = verify_relaxation_certificate(Sm.units, alpha0, dirs, P, phi)
            rel["certificate"] = {"support": len(phi), "verified": ok, "note": why}
        report["relaxation"] = rel
        print("relaxation", rel, flush=True)
    else:
        if len(dirs) > args.max_d:
            report["skipped"] = "d = %d exceeds --max-d" % len(dirs)
        else:
            counts, sats = exhaust(Sm, alpha0, dirs, C, P, args.lo, args.hi, rng, report, "exhaust")
            print("exhaust", counts, flush=True)
            for s in sats:
                print("SAT_FOUND", s["index"], s["lambda"], flush=True)
    report["seconds"] = round(time.time() - t0, 1)
    json.dump(report, open(args.out, "w"), indent=1)


if __name__ == "__main__":
    main()
