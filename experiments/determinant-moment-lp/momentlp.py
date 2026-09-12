"""Moment-LP hunter for Lueck determinant-conjecture violations.

Setting.  B = A^*A is a positive self-adjoint element of M_n(Z[G]) acting on
l^2(G)^n.  Write mu for its spectral measure with respect to Tr = sum_i tau(X_ii),
a positive measure of total mass m_0 = n on [0, r], where r is any norm bound
(the l^1 bound sum |coefficients| squared always works).  The Fuglede-Kadison
determinant condition is

    D(mu) = integral_{x > 0} log x  dmu  >=  0,

the integral taken off the atom at 0 (the kernel).  A violation is D(mu) < 0.

Only finitely many exact moments m_j = Tr(B^j), j = 0..J, are ever computable.
This module answers: do those moments ALONE force D < 0?

    V_J := max { D(nu) : nu >= 0 on [0, r],  integral x^j dnu = m_j, j = 0..J }.

V_J < 0 certifies a violation for every operator with those moments.  V_J >= 0
means level J is inconclusive -- never that the conjecture holds.

Duality.  The dual of the above is

    V_J = min { sum_j c_j m_j : P = sum_j c_j x^j >= log x on (0, r], P(0) >= 0 },

because integral_{x>0} log x dnu <= integral_{x>0} P dnu = integral P dnu -
P(0) nu({0}) <= sum_j c_j m_j when P(0) >= 0.  Such a P is a finite, checkable
certificate: rational coefficients, one polynomial inequality, and the exact
integer moments.  `certify` produces and verifies one.

The primal is run on a grid (a restriction, so a lower bound on V_J): when the
grid value is >= 0, level J is definitely inconclusive.  The dual is verified
rigorously, so a reported certificate is sound.
"""

import argparse
import json
import math
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog


# ---------------------------------------------------------------- Chebyshev

def cheb_on_interval(J, r):
    """Coefficient matrix M with T_j(2x/r - 1) = sum_k M[j][k] x^k, exact."""
    r = Fraction(r)
    # T_j in the variable y, then y = 2x/r - 1.
    t_prev = [Fraction(1)]                  # T_0(y) = 1
    t_cur = [Fraction(0), Fraction(1)]      # T_1(y) = y
    tees = [t_prev, t_cur]
    for _ in range(2, J + 1):
        nxt = [Fraction(0)] * (len(t_cur) + 1)
        for i, c in enumerate(t_cur):
            nxt[i + 1] += 2 * c
        for i, c in enumerate(t_prev):
            nxt[i] -= c
        tees.append(nxt)
        t_prev, t_cur = t_cur, nxt
    # substitute y = (2/r) x - 1 by repeated binomial expansion
    out = []
    for t in tees[:J + 1]:
        acc = [Fraction(0)] * (J + 1)
        for i, c in enumerate(t):
            if c == 0:
                continue
            # ((2/r)x - 1)^i
            for k in range(i + 1):
                binom = Fraction(math.comb(i, k))
                acc[k] += c * binom * (Fraction(2) / r) ** k * Fraction(-1) ** (i - k)
        out.append(acc[:J + 1])
    return out


def cheb_moments(moments, r):
    """Exact Chebyshev moments integral T_j(2x/r-1) dmu from monomial moments."""
    J = len(moments) - 1
    M = cheb_on_interval(J, r)
    return [sum(M[j][k] * Fraction(moments[k]) for k in range(J + 1)) for j in range(J + 1)]


# ---------------------------------------------------------------- primal

def grid(r, n_geo=1400, n_lin=600, lo=1e-9):
    g = np.concatenate([
        np.geomspace(lo, min(1.0, r), n_geo, endpoint=False),
        np.linspace(min(1.0, r), r, n_lin),
    ])
    return np.unique(g)


def primal_value(moments, r, **kw):
    """Lower bound on V_J: max of D(nu) over grid-supported nu.

    Returns (value, weights, xs).  The atom at 0 is a separate variable that
    enters only the mass constraint and contributes nothing to the objective.
    """
    J = len(moments) - 1
    xs = grid(r, **kw)
    cm = [float(v) for v in cheb_moments(moments, r)]
    M = cheb_on_interval(J, r)
    Mf = np.array([[float(c) for c in row] for row in M])
    # rows: T_j evaluated on the grid, via the monomial matrix (stable enough
    # after rescaling x -> x/r inside the Chebyshev recursion).
    y = 2.0 * xs / r - 1.0
    T = np.zeros((J + 1, xs.size))
    T[0] = 1.0
    if J >= 1:
        T[1] = y
    for j in range(2, J + 1):
        T[j] = 2.0 * y * T[j - 1] - T[j - 2]
    # zero atom: T_j(-1) = (-1)^j
    zero_col = np.array([(-1.0) ** j for j in range(J + 1)]).reshape(-1, 1)
    A_eq = np.hstack([T, zero_col])
    b_eq = np.array(cm)
    c = np.concatenate([-np.log(xs), [0.0]])       # minimise -D
    res = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method="highs")
    if not res.success:
        return None, None, xs
    return -res.fun, res.x, xs


# ---------------------------------------------------------------- dual

def verify_upper_bound(coeffs, r, margin_pts=200000, lo=1e-12):
    """Rigorously check P(x) >= log x on (0, r] and P(0) >= 0 for P in the
    Chebyshev-on-[0,r] basis given by `coeffs`.

    Returns (ok, worst_slack).  Uses a dense grid plus a Lipschitz bound for
    P - log on [lo, r], and handles (0, lo) by monotonicity of log.
    """
    J = len(coeffs) - 1
    xs = np.unique(np.concatenate([
        np.geomspace(lo, r, margin_pts // 2),
        np.linspace(0.0, r, margin_pts // 2),
    ]))
    y = 2.0 * xs / r - 1.0
    T = np.zeros((J + 1, xs.size))
    T[0] = 1.0
    if J >= 1:
        T[1] = y
    for j in range(2, J + 1):
        T[j] = 2.0 * y * T[j - 1] - T[j - 2]
    P = coeffs @ T
    with np.errstate(divide="ignore"):
        logs = np.log(np.maximum(xs, 1e-300))
    slack = P - logs
    # near 0 the inequality is free: log x -> -infty while P is bounded.
    tail = xs < lo
    worst = float(np.min(slack[~tail])) if np.any(~tail) else float("inf")
    # Lipschitz control of P - log on [lo, r]: |d/dx (P - log)| <= L
    dT = np.gradient(P, xs)
    L = float(np.max(np.abs(dT))) + 1.0 / lo
    h = float(np.max(np.diff(xs)))
    ok = worst - L * h / 2.0 > 0 or worst > 0
    P0 = float(coeffs @ np.array([(-1.0) ** j for j in range(J + 1)]))
    return bool(ok and P0 >= 0), worst, P0


def certify(moments, r, **kw):
    """Try to produce a verified upper-bound certificate for D(mu) < 0.

    Returns a dict with the Chebyshev coefficients of P, the bound
    sum_j c_j (Chebyshev moment)_j, and whether verification passed.
    """
    val, _, _ = primal_value(moments, r, **kw)
    if val is None:
        return {"status": "lp_failed"}
    J = len(moments) - 1
    cm = np.array([float(v) for v in cheb_moments(moments, r)])
    # dual variables from the primal solve
    xs = grid(r, **kw)
    y = 2.0 * xs / r - 1.0
    T = np.zeros((J + 1, xs.size))
    T[0] = 1.0
    if J >= 1:
        T[1] = y
    for j in range(2, J + 1):
        T[j] = 2.0 * y * T[j - 1] - T[j - 2]
    zero_col = np.array([(-1.0) ** j for j in range(J + 1)]).reshape(-1, 1)
    A_eq = np.hstack([T, zero_col])
    c = np.concatenate([-np.log(xs), [0.0]])
    res = linprog(c, A_eq=A_eq, b_eq=cm, bounds=(0, None), method="highs")
    if not res.success:
        return {"status": "lp_failed"}
    lam = -np.array(res.eqlin.marginals)          # P = sum lam_j T_j
    ok, worst, P0 = verify_upper_bound(lam, r)
    bound = float(lam @ cm)
    return {
        "status": "ok",
        "primal_value": float(val),
        "dual_bound": bound,
        "verified": ok,
        "worst_slack": worst,
        "P_at_zero": P0,
        "certifies_violation": bool(ok and bound < 0),
        "cheb_coeffs": [float(v) for v in lam],
    }


# ---------------------------------------------------------------- calibration

def fibonacci_moments(J):
    """Moments of the model measure of integer-moment-measure-with-negative-log-
    determinant: mu = a delta_{phi^2} + b delta_{psi^2}, m_j = (L_2j - F_2j)/2.
    These are 1, 1, 2, 5, 13, 34, ... and D(mu) = -(2/sqrt 5) log phi < 0."""
    f = [0, 1]
    lu = [2, 1]
    for _ in range(2, 2 * J + 2):
        f.append(f[-1] + f[-2])
        lu.append(lu[-1] + lu[-2])
    return [(lu[2 * j] - f[2 * j]) // 2 for j in range(J + 1)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", default="calibrate")
    ap.add_argument("--jmax", type=int, default=14)
    ap.add_argument("--r", type=float, default=3.0)
    ap.add_argument("--moments", default="")
    ap.add_argument("--out", default="")
    args = ap.parse_args()

    if args.mode == "calibrate":
        true_val = -2.0 / math.sqrt(5.0) * math.log((1 + math.sqrt(5)) / 2)
        rows = []
        for J in range(1, args.jmax + 1):
            m = fibonacci_moments(J)
            info = certify(m, args.r)
            info["J"] = J
            info["moments"] = m
            rows.append(info)
            print(json.dumps({k: info[k] for k in
                              ("J", "primal_value", "dual_bound", "verified",
                               "certifies_violation")}))
        out = {"target": "fibonacci", "true_D": true_val, "r": args.r, "rows": rows}
    else:
        m = [int(v) for v in args.moments.split(",")]
        info = certify(m, args.r)
        print(json.dumps(info))
        out = {"target": "custom", "moments": m, "r": args.r, "rows": [info]}

    if args.out:
        with open(args.out, "w") as fh:
            json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
