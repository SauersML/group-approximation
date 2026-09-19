#!/usr/bin/env python3
"""How much certified spectral radius one buys per unit of computation, for the two
certificate routes available for Thompson's F, and how far each is from ||P|| = 1.

Route M (moments): from the exact cogrowth terms c_0..c_N one gets the optimal bound
rho >= sqrt(theta*(N)) (moment_ceiling.py), and nothing better -- theta*(N) is the
minimum of sup supp over all positive measures with those moments.

Route W (windows): from a finite vertex set A in Cay(F, {x0^{+-1}, x1^{+-1}}) one gets
rho >= lambda_max(A_A)/4, best at A = B_r (ball_eigen.py).

Calibration (free group, 4-regular tree, rho = sqrt(3)/2 exactly): the two routes give
*identical* values when N = r, because the top Dirichlet eigenvector of a ball in a
tree is radial, the radial subspace is the Krylov space of delta_e, and the Rayleigh
maximum over a Krylov space of degree r is the largest Gauss node of the moment problem
with M_0..M_r.  In F the ball is not a tree ball and route W is strictly better at the
same r; this script measures the excess and extrapolates both.

No claim in this file is rigorous beyond the tabulated exact values: the fits are
three-point power-law fits, printed to show the *scale* of the remaining gap.
"""
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def tree_ball_eig(r):
    """lambda_max of the ball of radius r in the 4-regular tree, over 4."""
    import numpy as np
    n = r + 1
    T = np.zeros((n, n))
    for j in range(n - 1):
        v = 2.0 if j == 0 else math.sqrt(3.0)
        T[j, j + 1] = T[j + 1, j] = v
    return float(max(np.linalg.eigvalsh(T))) / 4


def tree_counts(N):
    c, cur = [1], {0: 1}
    for L in range(1, 2 * N + 1):
        nxt = {}
        for d, m in cur.items():
            nxt[d + 1] = nxt.get(d + 1, 0) + (4 if d == 0 else 3) * m
            if d > 0:
                nxt[d - 1] = nxt.get(d - 1, 0) + m
        cur = nxt
        if L % 2 == 0:
            c.append(cur.get(0, 0))
    return c


def tree_moment_bound(N):
    from moment_ceiling import optimum
    from fractions import Fraction
    c = tree_counts(N)
    M = [Fraction(x, 16 ** j) for j, x in enumerate(c)]
    lo, hi = optimum(M, N)
    return math.sqrt(float(lo))


def powerfit(pts):
    """Fit y = L - c * x^-alpha through three (x, y) points; return (L, c, alpha)."""
    (x1, y1), (x2, y2), (x3, y3) = pts

    def f(L):
        # alpha from two ratios must agree
        a = math.log((L - y1) / (L - y2)) / math.log(x2 / x1)
        b = math.log((L - y2) / (L - y3)) / math.log(x3 / x2)
        return a - b

    grid = [y3 + 1e-6 + k * (1.2 - y3) / 20000 for k in range(20000)]
    lo = hi = None
    prev = None
    for L in grid:
        try:
            val = f(L)
        except (ValueError, ZeroDivisionError):
            continue
        if prev is not None and prev[1] * val < 0:
            lo, hi = prev[0], L
            break
        prev = (L, val)
    if lo is None:
        return None, None, None
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(lo) * f(mid) <= 0:
            hi = mid
        else:
            lo = mid
    L = (lo + hi) / 2
    alpha = math.log((L - y1) / (L - y3)) / math.log(x3 / x1)
    c = (L - y3) * x3 ** alpha
    return L, c, alpha


def main():
    sys.path.insert(0, HERE)
    mom = json.load(open(os.path.join(HERE, "moment_ceiling.json")))
    rows = {r["N"]: r for r in mom["rows"]}
    out = {}

    # 1. free-group calibration: routes M and W coincide
    cal = []
    for r in (4, 6, 8, 10, 12):
        cal.append({"r": r, "tree_window": tree_ball_eig(r), "tree_moment_N_eq_r": tree_moment_bound(r)})
    out["free_group_calibration"] = cal
    out["free_group_routes_agree"] = all(abs(c["tree_window"] - c["tree_moment_N_eq_r"]) < 1e-9 for c in cal)

    # 2. the same comparison inside F
    try:
        win = json.load(open(os.path.join(HERE, "ball_eigen.json")))
    except OSError:
        win = None
    if win:
        comp = []
        for w in win["windows"]:
            r = w["r"]
            if r in rows:
                comp.append({"r": r, "ball": w["ball"],
                             "window_bound": w["certified_lower_bound"],
                             "moment_bound_N_eq_r": rows[r]["rho_certified"],
                             "excess": w["certified_lower_bound"] - rows[r]["rho_certified"]})
        out["F_window_vs_moment"] = comp
        xs = [(c["r"], c["excess"]) for c in comp if c["r"] >= 6]
        if len(xs) >= 3:
            out["excess_growth_per_radius"] = (xs[-1][1] - xs[0][1]) / (xs[-1][0] - xs[0][0])
        out["ball_growth_factor"] = comp[-1]["ball"] / comp[-2]["ball"] if len(comp) > 1 else None

    # 3. where route M is heading
    sel = [15, 23, 31]
    pts = [(N, rows[N]["rho_certified"]) for N in sel]
    L, c, alpha = powerfit(pts)
    out["moment_route_fit"] = {
        "points": pts, "limit": L, "coefficient": c, "exponent": alpha,
        "terms_needed_for": {str(t): (c / (L - t)) ** (1 / alpha) if t < L else None
                             for t in (0.92, 0.93, 0.95, 0.9682)},
        "comment": ("0.9682 = sqrt(15/16) is the Elvey Price-Guttmann extrapolation mu = 15.0. "
                    "The fitted limit of the certified sequence is below it, so the certified "
                    "sequence is nowhere near saturating the believed value; the fit is a "
                    "three-point power law and is not a proof of anything."),
    }
    if win and L:
        # radius at which a ball window would match the 32-term moment bound
        exc = out.get("excess_growth_per_radius", 0.0)
        target = rows[31]["rho_certified"]
        rr = None
        for r in range(13, 200):
            if L - c * r ** (-alpha) + exc * (r - 4) >= target:
                rr = r
                break
        g = out.get("ball_growth_factor") or 2.76
        out["window_route_projection"] = {
            "radius_to_match_32_term_moment_bound": rr,
            "ball_growth_factor_measured": g,
            "projected_vertices": (comp[-1]["ball"] * g ** (rr - comp[-1]["r"])) if rr else None,
            "comment": ("extrapolated with the measured excess-per-radius and the moment fit; "
                        "the exponent is what matters, not the exact radius."),
        }
    out["gap_to_amenability"] = {
        "certified_rho": rows[31]["rho_certified"],
        "ceiling_from_32_terms": math.sqrt(rows[31]["theta_upper"]),
        "distance_to_1": 1 - rows[31]["rho_certified"],
        "note": ("||P|| = 1 iff F is amenable.  No finite list of exact cogrowth terms can "
                 "prove ||P|| < 1 (thompson-f-moment-data-cannot-certify-nonamenability), and "
                 "the table above shows how slowly the complementary lower bound moves."),
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
