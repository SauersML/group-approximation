"""Monomial near-identity Torelli-winding census for Mod(S_2).

For a finite-index Gamma' <= Sp_4(Z) with preimage M' <= M = Mod(S_2), every
character psi : H_1(M') -> R/Z gives an honest monomial representation
rho = Ind_{M'}^{M} psi.  Since the Torelli group K lies in M', the separating
twist t_s acts diagonally: on the coset g_c M' by exp(2 pi i psi(V_c)), where
V_c = [g_c^{-1} t_s g_c] in H_1(M').  (census.py computes V_c and merges equal
vectors into classes j with multiplicity mult_j.)

Lift psi(V_j) to h_j in (-1/2, 1/2].  Then

    ||rho(t_s) - 1||_op = max_j |exp(2 pi i h_j) - 1|,
    kappa(rho(t_s))     = sum_j mult_j h_j                 (exactly),

and the vectors h that occur are exactly {h : B h in Z^r}, B a basis of the
relation lattice W = {w : sum w_j V_j = 0 in H_1(M')} (Hom(-, R/Z) is exact).

    e(Gamma') := inf { max_j |h_j| : B h in Z^r, sum_j mult_j h_j != 0 }.

(Z) restricted to monomial representations holds iff inf_{Gamma'} e > 0.

kappa lies in (1/q)Z, q = order of mult modulo W (q | 5, since t_s = 2 in
H_1(M) = Z/10 has order 5 and mult is the transfer of t_s).  If mult is not in
W (x) Q then e = 0 (a continuous family) -- this never happens below.

Upper bound: an exact rational h (MILP + exact projection).
Lower bound: short vectors w_1..w_k of W whose Q-span contains mult, with
||w_i||_1 <= L; then max|h| < 1/L forces <h, w_i> = 0, so kappa = 0: e >= 1/L.
"""
import json
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import census  # noqa: E402  (copy of the w11 census library, unchanged)


def lattice_data(name):
    """Return (index, B, mult, b1, tors) for the named case (as census.run)."""
    start, step = census.case(name)
    objs, act = census.enumerate_by_step(start, step, limit=200000)
    census.check_action(act)
    k = len(act)
    ngen, rels, vs = census.rs_data(act)
    cols, R, V = census.unit_eliminate(ngen, rels, vs)
    Rd = census.to_dense(R, cols)
    Vd = census.to_dense(V, cols)
    H = census.hnf_rows(Rd, len(cols)) if Rd else []
    b1, tors = census.h1_invariants(H, len(cols)) if H else (len(cols), [])
    classes, cls_of = {}, []
    for c in range(k):
        key = census.reduce_mod_hnf(Vd[c], H)
        if key not in classes:
            classes[key] = len(classes)
        cls_of.append(classes[key])
    reps = [None] * len(classes)
    mult = [0] * len(classes)
    for c in range(k):
        if reps[cls_of[c]] is None:
            reps[cls_of[c]] = c
        mult[cls_of[c]] += 1
    B = census.w_lattice(H, [Vd[c] for c in reps], len(cols))
    return k, B, mult, b1, tors


def order_mod_W(B, mult, qmax=60):
    """Least q >= 1 with q*mult in W; 0 if mult is not in W (x) Q."""
    import sympy
    m = len(mult)
    if B:
        rk = sympy.Matrix(B).rank()
        rk2 = sympy.Matrix(B + [mult]).rank()
    else:
        rk, rk2 = 0, (1 if any(mult) else 0)
    if rk2 > rk:
        return 0
    H = census.hnf_rows(B, m)
    for q in range(1, qmax + 1):
        if not any(census.reduce_mod_hnf([q * a for a in mult], H)):
            return q
    raise RuntimeError("order exceeds qmax")


def winding_milp(B, mult, q):
    """min t s.t. B h = n integer, |h_j| <= t, mult.h >= 1/q."""
    from scipy.optimize import Bounds, LinearConstraint, milp
    Bf = np.array(B, dtype=float)
    r, m = Bf.shape
    nv = m + r + 1
    c = np.zeros(nv)
    c[-1] = 1.0
    A_eq = np.hstack([Bf, -np.eye(r), np.zeros((r, 1))])
    A1 = np.hstack([np.eye(m), np.zeros((m, r)), -np.ones((m, 1))])
    A2 = np.hstack([-np.eye(m), np.zeros((m, r)), -np.ones((m, 1))])
    Ak = np.concatenate([np.array(mult, dtype=float), np.zeros(r + 1)])[None, :]
    cons = [LinearConstraint(A_eq, 0, 0),
            LinearConstraint(A1, -np.inf, 0),
            LinearConstraint(A2, -np.inf, 0),
            LinearConstraint(Ak, 1.0 / q, np.inf)]
    integrality = np.concatenate([np.zeros(m), np.ones(r), np.zeros(1)])
    lb = np.concatenate([np.full(m, -0.5), np.full(r, -1e6), [0]])
    ub = np.concatenate([np.full(m, 0.5), np.full(r, 1e6), [0.5]])
    res = milp(c, constraints=cons, integrality=integrality,
               bounds=Bounds(lb, ub), options={"time_limit": 900})
    if res.x is None:
        return None
    return res.x[:m], [int(round(v)) for v in res.x[m:m + r]], res.x[-1]


def exact_upper(B, mult, n, h0):
    """Exact rational h with B h = n near h0; return (max|h|, kappa, h)."""
    from fractions import Fraction
    import sympy
    Bs = sympy.Matrix(B)
    h0s = sympy.Matrix([sympy.Rational(Fraction(float(v)).limit_denominator(10**4))
                        for v in h0])
    ns = sympy.Matrix(n)
    corr = Bs.T * (Bs * Bs.T).solve(ns - Bs * h0s)
    h = h0s + corr
    assert Bs * h == ns
    kappa = sum(a * v for a, v in zip(mult, h))
    return max(abs(v) for v in h), kappa, h


def short_certificate(B, mult):
    """Least L such that W-vectors of l1-norm <= L (from an LLL basis and its
    pairwise sums/differences) span a Q-space containing mult.  Returns
    (L, list of vectors used).  Rigorous: e >= 1/L."""
    import sympy
    from flint import fmpz_mat
    r, m = len(B), len(mult)
    Lb = fmpz_mat(B).lll()
    base = [[int(Lb[i, j]) for j in range(m)] for i in range(r)]
    cand = {tuple(v) for v in base}
    if r <= 5:                                  # exhaustive, coefficients in [-3, 3]
        import itertools
        for co in itertools.product(range(-3, 4), repeat=r):
            v = tuple(sum(cc * base[i][j] for i, cc in enumerate(co))
                      for j in range(m))
            if any(v):
                cand.add(v)
    for i in range(r):
        for j in range(i + 1, r):
            for s in (1, -1):
                v = tuple(a + s * b for a, b in zip(base[i], base[j]))
                if any(v):
                    cand.add(v)
    cand = sorted(cand, key=lambda v: sum(abs(a) for a in v))
    used = []
    rk = 0
    for v in cand:
        M2 = sympy.Matrix(used + [list(v)])
        if M2.rank() > rk:
            used.append(list(v))
            rk += 1
            if sympy.Matrix(used + [mult]).rank() == rk:
                return sum(abs(a) for a in v), used
    return None, used


def certificate_at(B, mult, L):
    """Try to certify e >= 1/L: greedily collect w in W with ||w||_1 <= L
    until mult is in their Q-span.  At each step u = the component of mult
    orthogonal to the current span (scaled to an integer vector); if mult is
    spanned by short vectors, some short w has <u, w> != 0, and the MILP finds
    one with <u, w> >= 1 (w -> -w).  Returns the list of vectors or None."""
    import sympy
    from scipy.optimize import Bounds, LinearConstraint, milp
    Bf = np.array(B, dtype=float)
    r, m = Bf.shape
    used = []
    ms = sympy.Matrix(mult)
    for _ in range(r + 1):
        if used:
            S = sympy.Matrix(used).T                  # m x k
            coef = (S.T * S).solve(S.T * ms)
            u = ms - S * coef
        else:
            u = ms
        if all(v == 0 for v in u):
            return used
        den = sympy.ilcm(*[sympy.fraction(sympy.nsimplify(v))[1] for v in u])
        ui = [int(v * den) for v in u]
        g = 0
        for v in ui:
            g = int(np.gcd(g, v))
        ui = [v // g for v in ui]
        # variables: y (r ints), p (m reals >= |w|)
        c = np.concatenate([np.zeros(r), np.ones(m)])
        A1 = np.hstack([Bf.T, -np.eye(m)])
        A2 = np.hstack([-Bf.T, -np.eye(m)])
        Au = np.concatenate([np.array(ui, dtype=float) @ Bf.T, np.zeros(m)])[None, :]
        Al = np.concatenate([np.zeros(r), np.ones(m)])[None, :]
        cons = [LinearConstraint(A1, -np.inf, 0), LinearConstraint(A2, -np.inf, 0),
                LinearConstraint(Au, 1, np.inf), LinearConstraint(Al, -np.inf, L + 1e-9)]
        integ = np.concatenate([np.ones(r), np.zeros(m)])
        lb = np.concatenate([np.full(r, -1e4), np.zeros(m)])
        ub = np.concatenate([np.full(r, 1e4), np.full(m, np.inf)])
        res = milp(c, constraints=cons, integrality=integ, bounds=Bounds(lb, ub),
                   options={"time_limit": 600})
        if res.x is None:
            return None
        y = [int(round(v)) for v in res.x[:r]]
        w = [sum(B[i][j] * y[i] for i in range(r)) for j in range(m)]
        assert sum(abs(a) for a in w) <= L and sum(a * b for a, b in zip(ui, w)) >= 1
        used.append(w)
    return None


def sympy_rat(n):
    import sympy
    return sympy.Integer(n)


def run(name):
    t0 = time.time()
    k, B, mult, b1, tors = lattice_data(name)
    q = order_mod_W(B, mult)
    out = {"case": name, "index": k, "b1": b1, "torsion": tors,
           "classes": len(mult), "rank_W": len(B),
           "mult_set": sorted(set(mult)), "q_order_of_mult_mod_W": q}
    if q == 0:
        out["e"] = "0 (mult not in W (x) Q: continuous family)"
    else:
        # kappa in (1/q)Z; by h -> -h it suffices to impose kappa >= 1/q.
        sol = winding_milp(B, mult, q)
        if sol is not None:
            h0, n, t = sol
            ub, kap, h = exact_upper(B, mult, n, h0)
            out["e_upper_exact"] = str(ub)
            out["kappa_at_upper"] = str(kap)
            out["e_milp_float"] = float(t)
            out["h_upper"] = [str(v) for v in h]
        L, used = short_certificate(B, mult)
        if sol is not None and L is not None:
            Lt = int(round(1 / float(ub)))           # try to certify e >= e_upper
            if Lt < L and abs(1 / sympy_rat(Lt) - ub) == 0:
                used2 = certificate_at(B, mult, Lt)
                if used2 is not None:
                    L, used = Lt, used2
        out["cert_L"] = L
        out["e_lower"] = f"1/{L}" if L else None
        out["cert_vectors"] = used
    out["seconds"] = round(time.time() - t0, 1)
    return out


if __name__ == "__main__":
    names = sys.argv[1:] or ["sp4", "pt-2", "frame-2"]
    results = []
    for nm in names:
        res = run(nm)
        results.append(res)
        short = {a: b for a, b in res.items()
                 if a not in ("h_upper", "cert_vectors")}
        print(json.dumps(short), flush=True)
    here = os.path.dirname(os.path.abspath(__file__))
    fname = "windings-" + "_".join(names) + ".json"
    with open(os.path.join(here, fname), "w") as f:
        json.dump(results, f, indent=1)
