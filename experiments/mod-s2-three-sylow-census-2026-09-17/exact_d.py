#!/usr/bin/env python3
"""Exact (solver-independent) certificate for d >= 1/30.

census.distance_milp reports a floating-point MILP optimum.  Its upper bound
is exact (an explicit point of W^perp), but its lower bound is only a solver
claim.  This script proves the lower bound in exact rational arithmetic.

(1) d >= 1/30.  Lift W^perp to {h in R^m : B h in Z^r}, B a Z-basis of W,
    and write h = (1/3)1 + e.  If ||e||_inf <= 1/30 then row i of B gives
    k_i = (B h)_i in Z with |k_i - a_i/3| <= l_i/30 (a_i = aug, l_i = l1 of
    row i).  So k lies in a finite box; the script enumerates every k in it.
    For each k and every y in Q^r, weak duality gives
        ||e||_inf >= |y . (k - a/3)| / ||B^T y||_1   whenever B e = k - a/3.
    A float LP proposes y; the bound is then evaluated exactly with Fractions.
    If every k gets an exact bound >= 1/30, then d >= 1/30.
(2) The test "some theta in W^perp has 0 < theta_c < 1/10 for all c", which
    would exclude a positive relation of mass 10, is also run.  It finds no
    such theta at U, so A_+ = 20 stays a MILP value.
(3) The hypothesis (SG) of mod-s2-short-generated-torelli-relations-pin-
    one-thirtieth is checked on the LLL basis.  When it holds, that lemma
    gives d = 1/30 without the box of (1).

Usage: python3 exact_d.py <name>        run the fast Pbar pipeline for
                                        sylow.subgroup(name), save w-<name>.json
       python3 exact_d.py --check <w.json>   certify from a saved basis
"""
import json
import os
import sys
import time
from fractions import Fraction
from itertools import product

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sylow as S  # noqa: E402
C = S.C


def reduced_basis(B):
    """LLL-reduce B and check (exactly, by HNF) that the row lattice is W."""
    import flint
    L = flint.fmpz_mat(B).lll()
    R = [[int(L[i, j]) for j in range(L.ncols())] for i in range(L.nrows())]
    R = [r for r in R if any(r)]
    m = len(B[0])
    assert C.hnf_rows([list(r) for r in R], m) == C.hnf_rows(
        [list(r) for r in B], m), "LLL changed the lattice"
    return R


def lp_dual(Bf, c):
    """Float LP min ||e||_inf s.t. B e = c; return (value, dual y)."""
    from scipy.optimize import linprog
    r, m = Bf.shape
    cost = np.zeros(m + 1)
    cost[-1] = 1.0
    A_eq = np.hstack([Bf, np.zeros((r, 1))])
    A_ub = np.vstack([np.hstack([np.eye(m), -np.ones((m, 1))]),
                      np.hstack([-np.eye(m), -np.ones((m, 1))])])
    res = linprog(cost, A_ub=A_ub, b_ub=np.zeros(2 * m), A_eq=A_eq,
                  b_eq=np.array(c, dtype=float),
                  bounds=[(None, None)] * m + [(0, None)], method="highs")
    assert res.status == 0, res.message
    return res.fun, res.eqlin.marginals


def exact_bound(R, y, c):
    """|y.c| / ||R^T y||_1 in exact rationals (a valid lower bound)."""
    num = abs(sum(yi * ci for yi, ci in zip(y, c)))
    m = len(R[0])
    den = sum(abs(sum(y[i] * R[i][j] for i in range(len(R))))
              for j in range(m))
    return num / den if den else None


def rationalize(y, maxden):
    return [Fraction(float(v)).limit_denominator(maxden) for v in y]


def row_options(R, target):
    a = [sum(r) for r in R]
    opts = []
    for r, ai in zip(R, a):
        li = sum(abs(x) for x in r)
        lo = Fraction(ai, 3) - target * li
        hi = Fraction(ai, 3) + target * li
        k0 = -((-lo.numerator) // lo.denominator)       # ceil(lo)
        opts.append(list(range(k0, hi.numerator // hi.denominator + 1)))
    return a, opts


def certify_distance(R, target=Fraction(1, 30)):
    """Prove min ||e||_inf >= target over the lifted W^perp - (1/3)1."""
    t0 = time.time()
    a, opts = row_options(R, target)
    sizes = [len(o) for o in opts]
    nleaf = 1
    for s in sizes:
        nleaf *= s
    info = {"rows": len(R), "max_row_l1": max(sum(abs(x) for x in r)
                                              for r in R),
            "box_size": nleaf, "row_option_counts": sorted(set(sizes))}
    print(f"  box: {info}", flush=True)
    if nleaf == 0:
        info.update(certified=True, min_leaf_bound=None)
        return info
    assert nleaf <= 200000, "box too large; add branching"
    Bf = np.array(R, dtype=float)
    worst = None
    for k in product(*opts):
        c = [Fraction(ki) - Fraction(ai, 3) for ki, ai in zip(k, a)]
        val, y = lp_dual(Bf, [float(x) for x in c])
        best = None
        for maxden in (10, 100, 1000, 10 ** 5, 10 ** 8):
            lb = exact_bound(R, rationalize(y, maxden), c)
            if lb is not None and (best is None or lb > best):
                best = lb
            if best is not None and best >= target:
                break
        if best is None or best < target:
            info.update(certified=False, failing_k=list(k),
                        lp_value=val, exact_bound=str(best))
            return info
        if worst is None or best < worst:
            worst = best
    info.update(certified=True, min_leaf_bound=str(worst),
                seconds=round(time.time() - t0))
    return info


def exact_project(R, k, h0):
    """Exact projection of h0 onto {h : R h = k}, over Q (python-flint)."""
    import flint
    Rq = flint.fmpq_mat([[flint.fmpq(x) for x in r] for r in R])
    h = flint.fmpq_mat([[flint.fmpq(v.numerator, v.denominator)]
                        for v in h0])
    kq = flint.fmpq_mat([[flint.fmpq(x)] for x in k])
    G = Rq * Rq.transpose()
    z = G.solve(kq - Rq * h)
    hp = h + Rq.transpose() * z
    assert Rq * hp == kq
    return [Fraction(int(hp[i, 0].p), int(hp[i, 0].q))
            for i in range(hp.nrows())]


def certify_positive_floor(R, width=Fraction(1, 10)):
    """Find theta in W^perp with 0 < theta_c < width for all c (exactly)."""
    from scipy.optimize import Bounds, LinearConstraint, milp
    Bf = np.array(R, dtype=float)
    r, m = Bf.shape
    w = float(width)
    nv = m + r + 1                              # theta, k, s
    cost = np.zeros(nv)
    cost[-1] = -1.0                             # maximise the margin s
    A_eq = np.hstack([Bf, -np.eye(r), np.zeros((r, 1))])
    A_lo = np.hstack([np.eye(m), np.zeros((m, r)), -np.ones((m, 1))])
    A_hi = np.hstack([np.eye(m), np.zeros((m, r)), np.ones((m, 1))])
    cons = [LinearConstraint(A_eq, 0, 0),
            LinearConstraint(A_lo, 0, np.inf),      # theta_c >= s
            LinearConstraint(A_hi, -np.inf, w)]     # theta_c <= w - s
    integ = np.concatenate([np.zeros(m), np.ones(r), np.zeros(1)])
    lb = np.concatenate([np.zeros(m), np.full(r, -1e7), [0]])
    ub = np.concatenate([np.full(m, w), np.full(r, 1e7), [w / 2]])
    res = milp(cost, constraints=cons, integrality=integ,
               bounds=Bounds(lb, ub), options={"time_limit": 900})
    if res.x is None or res.x[-1] < 1e-7:
        return {"certified": False, "reason": "no interior point found"}
    k = [int(round(v)) for v in res.x[m:m + r]]
    h0 = [Fraction(float(v)).limit_denominator(10 ** 6) for v in res.x[:m]]
    h = exact_project(R, k, h0)
    ok = all(0 < v < width for v in h)
    return {"certified": ok, "margin": str(min(min(h), width - max(h))),
            "theta_denominators": sorted({v.denominator for v in h})[:6]}


def sg_split(R, extra=()):
    """(SG) via the splitting W = W_0 + Z w1, aug(w1) = 10.

    For a candidate w1 in W with aug 10, R_i' = R_i - (a_i/10) w1 spans
    W_0 = W cap ker(aug), and {R'} + {w1} spans W (checked by HNF).  An LLL
    basis of W_0 with all l1 <= 30 together with l1(w1) <= 20 is a generating
    set of W satisfying (SG)."""
    import flint
    m = len(R[0])
    a = [sum(r) for r in R]
    cands = [list(r) if sum(r) == 10 else [-x for x in r]
             for r in R if abs(sum(r)) == 10]
    cands += [list(w) for w in extra]
    cands = sorted(cands, key=lambda w: sum(abs(x) for x in w))[:6]
    hB = C.hnf_rows([list(r) for r in R], m)
    best = None
    for w1 in cands:
        assert sum(w1) == 10
        R0 = [[x - (ai // 10) * y for x, y in zip(r, w1)]
              for r, ai in zip(R, a)]
        L = flint.fmpz_mat(R0).lll()
        L0 = [[int(L[i, j]) for j in range(m)] for i in range(L.nrows())]
        L0 = [r for r in L0 if any(r)]
        assert all(sum(r) == 0 for r in L0)
        assert C.hnf_rows(L0 + [w1], m) == hB, "split does not span W"
        info = {"w1_l1": sum(abs(x) for x in w1), "w1_nonneg": min(w1) >= 0,
                "W0_rank": len(L0),
                "W0_max_l1": max(sum(abs(x) for x in r) for r in L0)}
        info["SG"] = info["w1_l1"] <= 20 and info["W0_max_l1"] <= 30
        if best is None or (info["SG"], -info["W0_max_l1"]) > (
                best["SG"], -best["W0_max_l1"]):
            best = info
    return best


def certify(B, label):
    t0 = time.time()
    R = reduced_basis(B)
    g = 0
    from math import gcd
    for r in R:
        g = gcd(g, sum(r))
    out = {"label": label, "classes": len(B[0]), "W_rank": len(R),
           "gcd_aug_W": g}
    # (SG) of mod-s2-short-generated-torelli-relations-pin-one-thirtieth:
    # every basis row has (aug 0, l1 <= 30) or (|aug| = 10, l1 <= 20).
    types = sorted({(abs(sum(r)), sum(abs(x) for x in r)) for r in R})
    sg = all((a == 0 and l <= 30) or (a == 10 and l <= 20) for a, l in types)
    out["short_generated"] = sg
    out["basis_row_types_abs_aug_l1"] = types
    # General form (SG*): aug in 10Z and the only integer n with
    # |n - aug/3| < l1/30 is 3 aug/10.  Checked in exact rationals.

    def forced(a, l):
        if a % 10:
            return False
        lo, hi = Fraction(a, 3) - Fraction(l, 30), Fraction(a, 3) + Fraction(l, 30)
        ns = [n for n in range(int(lo) - 1, int(hi) + 2) if lo < n < hi]
        return all(n == Fraction(3 * a, 10) for n in ns)
    out["short_generated_general"] = all(forced(sum(r), sum(abs(x) for x in r))
                                         for r in R)
    print(f"[{label}] short generation (SG): {sg}, general (SG*): "
          f"{out['short_generated_general']}; row types {types}", flush=True)
    if g == 10:
        pa, pw = S.positive_certificate(R)
        extra = [pw] if pa == 10 else []
        out["sg_split"] = sg_split(R, extra)
        out["short_generated_split"] = out["sg_split"]["SG"]
        print(f"[{label}] SG via W_0 + Z w1: {out['sg_split']}", flush=True)
    out["distance_ge_1/30"] = certify_distance(R)
    print(f"[{label}] distance: {out['distance_ge_1/30']}", flush=True)
    if g == 10:
        out["mass10_exclusion_test"] = certify_positive_floor(R)
        print(f"[{label}] mass-10 exclusion test: "
              f"{out['mass10_exclusion_test']}", flush=True)
    out["seconds"] = round(time.time() - t0)
    return out


def run_pipeline(name):
    """The fast Pbar pipeline of pbar.py, keeping the basis B of W."""
    import pbar
    kept = {}
    orig = S.lattice_from_rs

    def keep(*args, **kw):
        res = orig(*args, **kw)
        kept["B"] = res[1][4]
        return res
    S.lattice_from_rs = keep
    tmp = os.path.join(HERE, f".pbar-{name}-tmp.json")
    pbar.main(name, tmp, fast=True)
    summary = json.load(open(tmp))
    os.remove(tmp)
    return kept["B"], summary


if __name__ == "__main__":
    if sys.argv[1] == "--check":
        data = json.load(open(sys.argv[2]))
        out = certify(data["B"], data["name"])
        cpath = os.path.join(HERE, f"exact-{data['name']}.json")
        json.dump(out, open(cpath, "w"), indent=1)
        print("saved", cpath, flush=True)
    else:
        name = sys.argv[1]
        B, summary = run_pipeline(name)
        wpath = os.path.join(HERE, f"w-{name}.json")
        json.dump({"name": name, "summary": summary, "B": B},
                  open(wpath, "w"))
        print("saved", wpath, flush=True)
        out = certify(B, name)
        cpath = os.path.join(HERE, f"exact-{name}.json")
        json.dump(out, open(cpath, "w"), indent=1)
        print("saved", cpath, flush=True)
