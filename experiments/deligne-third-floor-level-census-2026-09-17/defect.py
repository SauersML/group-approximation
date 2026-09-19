"""mu_theta(X) = min_a max_(x,r) dist(hol_a(x,r) - theta k_r, Z) by MILP (HiGHS).

rho(s) e_x = e(a(x,s)) e_(s x).  hol(x, r) reads r = s_1...s_L right to left starting at x.
Returns (upper bound, dual lower bound, phases).
"""
from fractions import Fraction
import numpy as np
import scipy.sparse as sp
from scipy.optimize import milp, LinearConstraint, Bounds
from presentation import RELATORS, kvalues
from gsets import check

K = kvalues()


def cell_terms(perm, invp, x, r):
    """list of (var index (y,i), sign) for the holonomy of relator r at x."""
    terms = []
    y = x
    for (i, e) in reversed(r):
        if e > 0:
            terms.append(((y, i), 1))
            y = perm[i][y]
        else:
            y2 = invp[i][y]
            terms.append(((y2, i), -1))
            y = y2
    assert y == x
    return terms


def spanning_tree(perm):
    n = len(perm[0])
    seen = {0}
    tree = set()
    queue = [0]
    for x in queue:
        for i in range(5):
            y = perm[i][x]
            if y not in seen:
                seen.add(y)
                tree.add((x, i))
                queue.append(y)
    assert len(seen) == n
    return tree


def build(perm, theta, relators=RELATORS):
    invp = check(perm, relators)
    n = len(perm[0])
    nvar_a = 5 * n
    cells = [(x, name) for name in relators for x in range(n)]
    ncell = len(cells)
    nv = nvar_a + ncell + 1  # a, n, t
    rows, cols, vals = [], [], []
    lo, hi = [], []
    for c, (x, name) in enumerate(cells):
        r = relators[name]
        coef = {}
        for (y, i), s in cell_terms(perm, invp, x, r):
            v = 5 * y + i
            coef[v] = coef.get(v, 0) + s
        # hol - n - t <= theta k ;  hol - n + t >= theta k
        for sign, (l, h) in ((+1, (-np.inf, 0.0)), (-1, (0.0, np.inf))):
            row = len(lo)
            for v, cf in coef.items():
                if cf:
                    rows.append(row); cols.append(v); vals.append(cf)
            rows.append(row); cols.append(nvar_a + c); vals.append(-1)
            rows.append(row); cols.append(nv - 1); vals.append(-sign)
            tk = float(theta * K[name])
            lo.append(l + tk); hi.append(h + tk)
    A = sp.csr_matrix((vals, (rows, cols)), shape=(len(lo), nv))
    lb = np.zeros(nv); ub = np.ones(nv)
    for (x, i) in spanning_tree(perm):
        ub[5 * x + i] = 0.0
    for c, (x, name) in enumerate(cells):
        r = relators[name]
        pos = sum(1 for (_, e) in r if e > 0); neg = len(r) - pos
        tk = float(theta * K[name])
        lb[nvar_a + c] = np.floor(-neg - tk) - 1
        ub[nvar_a + c] = np.ceil(pos - tk) + 1
    lb[nv - 1] = 0.0; ub[nv - 1] = 0.5
    integ = np.zeros(nv); integ[nvar_a:nvar_a + ncell] = 1
    cost = np.zeros(nv); cost[nv - 1] = 1.0
    return cost, A, lo, hi, lb, ub, integ, nvar_a


def mu(perm, theta, time_limit=600, relators=RELATORS, verbose=False):
    cost, A, lo, hi, lb, ub, integ, nvar_a = build(perm, theta, relators)
    res = milp(cost, constraints=LinearConstraint(A, lo, hi), integrality=integ,
               bounds=Bounds(lb, ub),
               options={"time_limit": time_limit, "disp": verbose, "mip_rel_gap": 1e-9})
    if res.x is None:
        return None, getattr(res, "mip_dual_bound", None), None
    return res.fun, getattr(res, "mip_dual_bound", None), res.x[:nvar_a]


def defect_of(perm, theta, a, relators=RELATORS):
    """Independent re-evaluation of the uniform defect of phases a (certifies upper bounds)."""
    invp = check(perm, relators)
    n = len(perm[0])
    worst = 0.0
    for name, r in relators.items():
        for x in range(n):
            h = sum(s * a[5 * y + i] for (y, i), s in cell_terms(perm, invp, x, r))
            d = h - theta * K[name]
            worst = max(worst, abs(d - round(d)))
    return worst
