"""Monomial operator-norm t-defect mu_t(X) for the Deligne cover of SL_2(Z[1/2]) on finite SL_2(Z[1/2])-sets X.

mu_t(X) = min over real phases a[s,p] and integers n[r,p] of max_(r,p) |hol_(r,p)(a) - t k_r - n[r,p]|,
the l^inf distance from t*kappa to delta C^1(R) + C^2(Z) on the Schreier 2-complex Y_X (w14 convention).
Presentation and k_r from lifts.py (k = 1 on x^4, 0 elsewhere).  X is built from SL_2(Z/N), N odd.
Usage: python3 sl2_milp.py SETNAME [t_num t_den] [time_limit]
"""
import sys, json, time, itertools
from fractions import Fraction
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds, linprog
from scipy.sparse import lil_matrix, csr_matrix, vstack, hstack, eye as speye
from lifts import RELATORS, K

GENS = ["x", "y", "X", "Y"]

def gen_mats(N):
    h = pow(2, -1, N)
    return {"x": ((0, N - 1), (1, 0)), "y": ((0, N - 1), (1, 1)),
            "X": ((0, (-2) % N), (h, 0)), "Y": ((0, (-2) % N), (h, 1))}

def mul(P, Q, N):
    return tuple(tuple(sum(P[i][k] * Q[k][j] for k in range(2)) % N for j in range(2)) for i in range(2))

def orbit_action(N, start, act):
    """act(M, p) -> p' (left action of a matrix mod N); returns list of 4 permutation arrays and the point list."""
    M = gen_mats(N)
    pts = [start]; idx = {start: 0}; i = 0
    while i < len(pts):
        p = pts[i]
        for s in GENS:
            q = act(M[s], p)
            if q not in idx:
                idx[q] = len(pts); pts.append(q)
        i += 1
    perms = {s: np.array([idx[act(M[s], p)] for p in pts]) for s in GENS}
    return perms, pts

def act_vec(N):
    return lambda M, v: ((M[0][0] * v[0] + M[0][1] * v[1]) % N, (M[1][0] * v[0] + M[1][1] * v[1]) % N)

def act_proj(N, units):
    def f(M, v):
        w = act_vec(N)(M, v)
        return min(((u * w[0]) % N, (u * w[1]) % N) for u in units)
    return f

def act_left_mult(N):
    return lambda M, g: mul(M, g, N)

def units_mod(N):
    from math import gcd
    return [u for u in range(1, N) if gcd(u, N) == 1]

def SETS(name):
    if name == "point":
        return {s: np.array([0]) for s in GENS}
    kind, N = name.split("_")[0] + "_", int(name.split("_")[1])
    if kind == "P1_":       # projective line over Z/N (lines through primitive vectors)
        return orbit_action(N, (1, 0), act_proj(N, units_mod(N)))[0]
    if kind == "V_":        # primitive vectors
        return orbit_action(N, (1, 0), act_vec(N))[0]
    if kind == "PV_":       # primitive vectors up to sign
        return orbit_action(N, (1, 0), act_proj(N, [1, N - 1]))[0]
    if kind == "SL_":       # regular SL_2(Z/N)
        return orbit_action(N, ((1, 0), (0, 1)), act_left_mult(N))[0]
    raise KeyError(name)

def build_cells(perms):
    """Rows = 2-cells (relator r, basepoint p); columns = 1-cells (s, p); entries = signed incidence; kappa = k_r."""
    n = len(perms["x"]); col = {(s, p): i for i, (s, p) in enumerate(itertools.product(GENS, range(n)))}
    inv = {s: np.argsort(perms[s]) for s in GENS}
    rows, kap, names = [], [], []
    for r, word in RELATORS.items():
        for p in range(n):
            row = {}; q = p
            for s, e in reversed(word):          # rho(s1)...rho(sm) e_p: apply sm first
                if e == 1:
                    row[col[(s, q)]] = row.get(col[(s, q)], 0) + 1; q = perms[s][q]
                else:
                    q = inv[s][q]; row[col[(s, q)]] = row.get(col[(s, q)], 0) - 1
            assert q == p, (r, p)
            rows.append(row); kap.append(K[r]); names.append((r, p))
    A = lil_matrix((len(rows), len(col)))
    for i, row in enumerate(rows):
        for j, v in row.items():
            if v:
                A[i, j] = v
    return A.tocsr(), np.array(kap, float), names, col

def tree_edges(perms, col):
    n = len(perms["x"]); seen = {0}; stack = [0]; T = []
    while stack:
        p = stack.pop()
        for s in GENS:
            q = perms[s][p]
            if q not in seen:
                seen.add(q); stack.append(q); T.append(col[(s, p)])
    assert len(seen) == n, "X not transitive"
    return T

def mu_milp(perms, t, time_limit=600, eps_cap=0.5):
    A, kap, names, col = build_cells(perms)
    m, E = A.shape
    c = kap * t
    T = set(tree_edges(perms, col)); keep = [e for e in range(E) if e not in T]
    A = A[:, keep].tocsr(); E = len(keep)
    Apos = A.maximum(0); Aneg = (-A).maximum(0)
    nlo = np.floor(-np.array(Aneg.sum(axis=1)).ravel() - c - eps_cap)
    nhi = np.ceil(np.array(Apos.sum(axis=1)).ravel() - c + eps_cap)
    one = csr_matrix(np.ones((m, 1))); I = speye(m, format="csr")
    Aub = vstack([hstack([A, -I, -one]), hstack([-A, I, -one])]).tocsr()
    lo = np.full(2 * m, -np.inf); hi = np.concatenate([c, -c])
    cost = np.zeros(E + m + 1); cost[-1] = 1
    integ = np.concatenate([np.zeros(E), np.ones(m), [0]])
    lb = np.concatenate([np.zeros(E), nlo, [0]]); ub = np.concatenate([np.ones(E), nhi, [eps_cap]])
    res = milp(cost, constraints=LinearConstraint(Aub, lo, hi), integrality=integ, bounds=Bounds(lb, ub),
               options=dict(time_limit=time_limit, disp=False, mip_rel_gap=1e-9))
    x = res.x
    return dict(status=res.status, msg=res.message, eps=None if x is None else x[-1],
                bound=getattr(res, "mip_dual_bound", None), cells=m, edges=E, sol=x, A=A, names=names)

def kahler_norm(perms):
    """||kappa_R||_cell = min over real a of max |k - delta a| (LP)."""
    A, kap, _, col = build_cells(perms)
    m, E = A.shape
    one = csr_matrix(np.ones((m, 1)))
    Aub = vstack([hstack([A, -one]), hstack([-A, -one])]).tocsr()
    b = np.concatenate([kap, -kap])
    cost = np.zeros(E + 1); cost[-1] = 1
    res = linprog(cost, A_ub=Aub, b_ub=b, bounds=[(None, None)] * E + [(0, None)], method="highs")
    return res.fun

if __name__ == "__main__":
    name = sys.argv[1]
    t = Fraction(int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else Fraction(1, 3)
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 600
    perms = SETS(name); t0 = time.time()
    kn = kahler_norm(perms)
    r = mu_milp(perms, float(t), tl)
    eps = r["eps"]
    print(json.dumps(dict(name=name, t=str(t), npts=len(perms["x"]), cells=r["cells"], status=r["status"],
                          eps=eps, frac=None if eps is None else str(Fraction(eps).limit_denominator(2000)),
                          dual_bound=r["bound"], kahler=kn,
                          kahler_frac=str(Fraction(kn).limit_denominator(2000)), secs=round(time.time() - t0, 1)),
                     default=float), flush=True)
