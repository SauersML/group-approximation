#!/usr/bin/env python3
"""Linear screen for left-invertible lifts of s0 in S_- = eps_- F_3[L_{F_3}(1,2)^x].

If alpha in S_- has pi(alpha) = s0 and beta alpha = 1 + n with n nilpotent, then (1+n)^-1 beta is a
left inverse of alpha, and alpha beta' != 1 because pi(alpha) = s0 has no right inverse in R. So S_-
is not directly finite and the unit group is not surjunctive (ternary-invisible-pair route,
condition (V3*) of research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md).

For a fixed lift alpha the condition is linear in beta in span(C) and n in span{1 - [p] : p in P},
with P a finite 3-group (level-m unitriangular transvections), whose augmentation ideal is
nilpotent. UNSAT for an instance means: no such beta, n with those supports for that alpha.

Controls: (C1) the solver on monomials of R finds t0 s0 = 1; (C2) alpha = [g] finds [g^-1];
(C3) alpha = e_- has no left inverse, so the screen must return UNSAT; (C4) no lift of s0 is
supported on Thompson's V alone (the all-ones vector of the Cantor module is fixed).
Run on MSI only.
"""

import argparse
import itertools
import json
import random
import sys
import time

import tleavitt as L


LAST_STATS = {}


class Eliminator(object):
    """Sparse Gaussian elimination over F_3 on column vectors keyed by basis keys."""

    def __init__(self):
        self.piv = {}
        self.order = []

    def _reduce(self, vec, combo):
        while True:
            hit = next((k for k in vec if k in self.piv), None)
            if hit is None:
                return vec, combo
            pv, pc = self.piv[hit]
            f = vec[hit]
            vec = L.add(vec, pv, -f)
            combo = L.add(combo, pc, f)

    def insert(self, j, col):
        rem, coeffs = self._reduce(dict(col), {})
        if rem:
            k = next(iter(rem))
            inv = rem[k]  # 1 or 2, its own inverse mod 3
            pv = L.scale(rem, inv)
            pc = L.scale(L.add({j: 1}, coeffs, -1), inv)
            self.piv[k] = (pv, pc)
            self.order.append(k)

    def solve(self, rhs):
        rem, coeffs = self._reduce(dict(rhs), {})
        return None if rem else coeffs

    def dual_certificate(self, rhs):
        """A functional phi with phi(column) = 0 for every inserted column and phi(rhs) = 1.

        The remainder of rhs vanishes on every pivot coordinate; put phi = 1/rem[j0] at one
        nonpivot j0 and fill pivots in reverse insertion order, since each pivot vector vanishes
        on the pivots inserted before it.
        """
        rem, _ = self._reduce(dict(rhs), {})
        if not rem:
            return None
        j0 = next(iter(rem))
        phi = {j0: rem[j0]}  # 1/1 = 1, 1/2 = 2 over F_3
        for k in reversed(self.order):
            pv = self.piv[k][0]
            s = sum(c * phi.get(j, 0) for j, c in pv.items() if j != k) % 3
            if s:
                phi[k] = (-s) % 3
        return phi


def verify_dual_certificate(family_keys, alpha, P_units, phi, sample_dual=150, rng=None,
                            alpha_units=None):
    """Recompute every column from a fresh registry and check phi . column = 0, phi(1) != 0."""
    Sm2 = L.SMinus()
    units = family_keys
    alpha_units = alpha_units or units
    one = Sm2.one()
    (k1, c1), = one.items()
    if phi.get(k1, 0) % 3 == 0:
        return False, "phi(1) = 0"
    alpha2 = {}
    for k, c in alpha.items():
        alpha2 = L.add(alpha2, Sm2.of_unit(alpha_units[k], c))
    checked = 0
    for k, u in units.items():
        col = Sm2.mul(Sm2.of_unit(u), alpha2)
        if sum(c * phi.get(kk, 0) for kk, c in col.items()) % 3:
            return False, "phi does not kill column of a C unit"
    for p in P_units:
        col = L.add(Sm2.of_unit(p), one, -1)
        if sum(c * phi.get(kk, 0) for kk, c in col.items()) % 3:
            return False, "phi does not kill a correction column"
    if rng is not None:
        L.set_dual(True)
        pool = list(units.values())
        for _ in range(sample_dual):
            x, y = rng.choice(pool), rng.choice(pool)
            if L._maxbeta(x.val) + L._maxbeta(y.val) <= 13:
                L.mul(x.val, y.val)
                checked += 1
        L.set_dual(False)
    return True, "ok, %d sampled products dual-checked" % checked


def family(name):
    tu = L.thompson_unit
    gens = {}
    if name in ("v", "vwd", "mix"):
        gens["A"] = tu(["0", "10", "11"], ["00", "01", "1"])
        gens["B"] = tu(["0", "10", "110", "111"], ["0", "100", "101", "11"])
        gens["C"] = tu(["0", "10", "11"], ["11", "0", "10"])
        gens["P"] = tu(["0", "10", "11"], ["10", "0", "11"])
    if name in ("mix", "mix2"):
        gens["A2"] = tu(["00", "01", "1"], ["00", "1", "01"])
    if name == "mix2":
        gens["A"] = tu(["0", "10", "11"], ["00", "01", "1"])
        gens["W"], gens["D"] = L.W, L.D
        gens["sig00"] = L.diagonal_unit(["00", "01", "1"], [2, 1, 1])
        gens["sig01"] = L.diagonal_unit(["00", "01", "1"], [1, 2, 1])
    if name in ("vwd", "eld3", "mix"):
        gens["W"], gens["D"] = L.W, L.D
    if name in ("eld3", "mix"):
        alpha = ["000", "001", "01"]
        ring = {"1": L.ONE, "s0": L.s0, "s1": L.s1, "t0": L.t0, "t1": L.t1}
        for i, j in itertools.permutations(range(3), 2):
            for rn, r in ring.items():
                n = L.mul(L.mul(L.S(alpha[i]), r), L.T(alpha[j]))
                gens["E%d%d_%s" % (i, j, rn)] = L.one_plus_nilpotent(n)
        dom = alpha + ["1000", "1001", "101"] + ["1100", "1101", "111"]
        zeta = ["100", "101", "11"]
        gens["u"] = tu(dom, [a + "0" for a in alpha] + [a + "1" for a in alpha] + zeta)
        gens["v"] = tu(dom, [a + "0" for a in alpha] + zeta + [a + "1" for a in alpha])
    if not gens:
        raise ValueError(name)
    return gens


def ball(Sm, gens, radius):
    steps = []
    for g in gens.values():
        steps += [g, g.inverse()]
    seen = {Sm.basis(L.IDENTITY)[0]: L.IDENTITY}
    frontier = [L.IDENTITY]
    for _ in range(radius):
        nxt = []
        for x in frontier:
            for s in steps:
                y = x * s
                k = Sm.basis(y)[0]
                if k not in seen:
                    seen[k] = Sm.units[k]
                    nxt.append(y)
        frontier = nxt
    return list(seen.keys())


def unitriangular(level):
    cyl = ["".join(b) for b in itertools.product("01", repeat=level)]
    gens = []
    for i, j in itertools.combinations(range(len(cyl)), 2):
        gens.append(L.one_plus_nilpotent(L.mul(L.S(cyl[i]), L.T(cyl[j]))))
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
    return list(group.values())


def explicit_s0_lift(Sm):
    """s0 = A q_0 + A' q_1 with q_0 = 2(1 + D), q_1 = 2(1 - D): support four in S_-."""
    A = L.thompson_unit(["0", "10", "11"], ["00", "01", "1"])
    A2 = L.thompson_unit(["00", "01", "1"], ["00", "1", "01"])
    alpha = {}
    for u, c in ((A, 2), (A * L.D, 2), (A2, 2), (A2 * L.D, 1)):
        alpha = L.add(alpha, Sm.of_unit(u, c))
    if Sm.evaluate(alpha) != L.s0:
        raise AssertionError("explicit lift does not evaluate to s0")
    return alpha


def kernel_perturbations(Sm, base, keys, samples, rng):
    """base + random combinations of ker(pi) vectors inside span(keys)."""
    el2, kernel = Eliminator(), []
    for j, k in enumerate(keys):
        col = Sm.units[k].val
        rem, coeffs = el2._reduce(dict(col), {})
        if not rem:
            kernel.append({keys[i]: c for i, c in L.add({j: 1}, coeffs, -1).items() if c})
        else:
            el2.insert(j, col)
    out = []
    for _ in range(samples if kernel else 0):
        x = dict(base)
        for vec in rng.sample(kernel, min(3, len(kernel))):
            signed = {}
            for k, c in vec.items():
                signed = L.add(signed, {k: c})
            x = L.add(x, signed, rng.choice((1, 2)))
        assert Sm.evaluate(x) == L.s0
        out.append(x)
    return out, len(kernel)


def lifts_of(Sm, keys, target, samples, rng):
    """Particular and randomly perturbed solutions of pi(sum lambda_g [g]) = target."""
    el = Eliminator()
    for j, k in enumerate(keys):
        el.insert(j, Sm.units[k].val)
    base = el.solve(target)
    if base is None:
        return []
    out = [{keys[j]: c for j, c in base.items() if c}]
    kernel = []
    el2 = Eliminator()
    for j, k in enumerate(keys):
        col = Sm.units[k].val
        rem, coeffs = el2._reduce(dict(col), {})
        if not rem:
            kernel.append(L.add({j: 1}, coeffs, -1))
        else:
            el2.insert(j, col)
    for _ in range(samples if kernel else 0):
        x = dict(base)
        for vec in rng.sample(kernel, min(3, len(kernel))):
            x = L.add(x, vec, rng.choice((1, 2)))
        out.append({keys[j]: c for j, c in x.items() if c})
    return out


def image_feasible(Sm, alpha, C, P):
    """The same system after pi: beta' in pi(span C), n' in span{p - 1}, beta' pi(alpha) = 1 + n'.

    If this fails, UNSAT upstairs is vacuous: the supports cannot even carry a left inverse of s0 in R.
    """
    a = Sm.evaluate(alpha)
    el = Eliminator()
    cols = [L.mul(Sm.units[k].val, a) for k in C]
    cols += [L.add(p.val, L.ONE, -1) for p in P if not L.is_one(p.val)]
    for j, col in enumerate(cols):
        el.insert(j, col)
    return el.solve(L.ONE) is not None


def left_inverse_screen(Sm, alpha, C, P):
    one = Sm.one()
    el = Eliminator()
    cols = {}
    for k in C:
        cols[("c", k)] = Sm.mul({k: 1}, alpha)
    for p in P:
        pk = Sm.of_unit(p)
        if pk == one:
            continue
        cols[("p", L.key(p.val))] = L.add(pk, one, -1)  # -(1 - [p]) moved to the left side
    names = list(cols)
    for j, name in enumerate(names):
        el.insert(j, cols[name])
    rows = set()
    for vec in cols.values():
        rows.update(vec)
    LAST_STATS.clear()
    LAST_STATS.update(columns=len(names), rows=len(rows), rank=len(el.piv))
    sol = el.solve(one)
    if sol is None:
        LAST_STATS["phi"] = el.dual_certificate(one)
        return None
    return {names[j]: c for j, c in sol.items()}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--family", default="eld3")
    ap.add_argument("--lift-radius", type=int, default=1)
    ap.add_argument("--radius", type=int, default=2)
    ap.add_argument("--level", type=int, default=2)
    ap.add_argument("--samples", type=int, default=4)
    ap.add_argument("--controls-only", action="store_true")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    rng = random.Random(20260914)
    report = {"args": vars(args), "controls": {}, "instances": []}
    t = time.time()
    Sm = L.SMinus()
    # C1: monomials of R, alpha = s0
    mons = [L.elem([((a, b), 1)]) for a in ("", "0", "1") for b in ("", "0", "1")
            if not (a.endswith("1") and b.endswith("1"))]
    el = Eliminator()
    for j, m in enumerate(mons):
        el.insert(j, L.mul(m, L.s0))
    report["controls"]["C1_leavitt_t0_s0"] = el.solve(L.ONE) is not None
    gens = family(args.family)
    B1 = ball(Sm, gens, 1)
    P = unitriangular(args.level)
    g = Sm.units[B1[1]]
    report["controls"]["C2_unit_left_inverse"] = left_inverse_screen(
        Sm, {B1[1]: 1}, [Sm.basis(g.inverse())[0]], P[:1]) is not None
    e_minus = L.scale(L.add(Sm.one(), Sm.of_unit(L.W)), 2)
    B2c = ball(Sm, family("vwd"), 2)
    report["controls"]["C3_e_minus_unsat"] = left_inverse_screen(Sm, e_minus, B2c, P) is None
    phi3 = LAST_STATS.pop("phi", None)
    report["controls_stats_C3"] = dict(LAST_STATS)
    ok3, _ = verify_dual_certificate({k: Sm.units[k] for k in B2c}, e_minus, P, phi3 or {},
                                     alpha_units=Sm.units)
    report["controls"]["C3_dual_certificate_verifies"] = bool(phi3) and ok3
    if phi3:
        bad = dict(phi3)
        kbad = next(k for k in bad if k not in Sm.one())
        bad[kbad] = (bad[kbad] + 1) % 3
        okbad, _ = verify_dual_certificate({k: Sm.units[k] for k in B2c}, e_minus, P, bad,
                                           alpha_units=Sm.units)
        report["controls"]["C3_corrupted_certificate_rejected"] = not okbad
    p0 = Sm.of_unit(P[1])
    alpha5 = L.add(L.scale(Sm.one(), 2), p0, -1)  # 1 + (1 - [p0]), a unit needing the correction
    report["controls"]["C5_nilpotent_correction_found"] = left_inverse_screen(
        Sm, alpha5, [B1[0]], P) is not None
    Vb = ball(Sm, family("v"), 2)
    report["controls"]["C4_no_s0_lift_in_V"] = not lifts_of(Sm, Vb, L.s0, 0, rng)
    print("controls", report["controls"], "%.1fs" % (time.time() - t), flush=True)
    if not all(report["controls"].values()) or args.controls_only:
        json.dump(report, open(args.out, "w"), indent=1)
        sys.exit(0 if all(report["controls"].values()) else 2)
    lift_keys = ball(Sm, gens, args.lift_radius)
    C = ball(Sm, gens, args.radius)
    alpha4 = explicit_s0_lift(Sm)
    perturbed, kdim = kernel_perturbations(Sm, alpha4, lift_keys, args.samples, rng)
    report["sizes"] = {"lift_ball": len(lift_keys), "C": len(C), "P": len(P),
                       "kernel_vectors_in_lift_ball": kdim}
    for alpha in [alpha4] + perturbed:
        assert Sm.evaluate(alpha) == L.s0
        t1 = time.time()
        sol = left_inverse_screen(Sm, alpha, C, P)
        phi = LAST_STATS.pop("phi", None)
        inst = {"support": len(alpha), "sat": sol is not None, "seconds": round(time.time() - t1, 1),
                "stats": dict(LAST_STATS), "image_feasible": image_feasible(Sm, alpha, C, P)}
        if phi is not None:
            ok, why = verify_dual_certificate({k: Sm.units[k] for k in C}, alpha, P, phi, rng=rng,
                                              alpha_units=Sm.units)
            inst["dual_certificate"] = {"support": len(phi), "verified": ok, "note": why}
        if sol is not None:
            inst["alpha"] = [[list(map(list, k)), c] for k, c in alpha.items()]
            inst["solution"] = [[n[0], [list(map(list, n[1])) if n[0] == "c" else list(map(list, n[1]))], c]
                                for n, c in sol.items()]
        report["instances"].append(inst)
        print(inst["support"], inst["sat"], inst["seconds"], flush=True)
    json.dump(report, open(args.out, "w"), indent=1)


if __name__ == "__main__":
    main()
