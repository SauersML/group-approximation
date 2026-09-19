"""Monomial 1/3-defect census on Schreier complexes Y_X of Sp_4(Z) (Birman-Hilden presentation).

mu(X) = min over theta in R^{edges}, n in Z^{cells} of  max_cells | (A theta)(c) - k_c/3 - n_c |
(in turns; A = cellular coboundary on edges, k_c = universal-cover lift exponent of the relator of cell c).
Equivalently mu(X) = (1/3) min { ||u||_* : u in Hom(Z_2(Y_X;Z),Z), u = kappa mod 3 },
||u||_* = sup over real 2-cycles b of u(b)/||b||_1.

Upper bounds: alternating rounding / LP (exact LP for each fixed rounding n).
Lower bounds: integer 2-cycle certificates b: mu >= dist(kappa(b)/3, Z)/||b||_1 (valid for every n).
Exact MILP (HiGHS) for small X.
"""
import numpy as np, json, sys, time, itertools
from fractions import Fraction
from scipy.optimize import linprog, milp, LinearConstraint, Bounds
from scipy.sparse import csr_matrix, lil_matrix, hstack, vstack, eye as speye
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from bh_lifts import relators, GEN, NS

REL = relators()
KAP = {"chain6": 3, "iota2": 2, "sep": 1}  # |winding|; overall sign irrelevant (complex conjugation)

# ---------------- finite Sp_4(Z)-sets ----------------
def orbit_action(start, act):
    """start: hashable point; act(g_index, point)->point. BFS orbit; returns perms (5 arrays) and point list."""
    pts = [start]; idx = {start: 0}; i = 0
    while i < len(pts):
        p = pts[i]
        for g in range(5):
            q = act(g, p)
            if q not in idx: idx[q] = len(pts); pts.append(q)
        i += 1
    perms = [np.array([idx[act(g, p)] for p in pts]) for g in range(5)]
    return perms, pts

def mat_mod(N):
    return [(g % N).astype(np.int64) for g in GEN]

def vec_action(N, normalize=None):
    Ms = mat_mod(N)
    def act(g, v):
        w = tuple(int(x) for x in (np.array(v) @ Ms[g]) % N)  # right action on row vectors
        return normalize(w) if normalize else w
    return act

def proj_norm(p):
    def nz(w):
        for x in w:
            if x % p:
                inv = pow(int(x), -1, p); return tuple((inv * y) % p for y in w)
        return w
    return nz

def X_vectors(N, v0=(1, 0, 0, 0)):
    return orbit_action(tuple(v0), vec_action(N))

def X_proj(p):
    return orbit_action((1, 0, 0, 0), vec_action(p, proj_norm(p)))

def X_subspace(N, basis, canon):
    """orbit of a subspace/tuple under Sp_4(Z/N); canon: canonical form of a tuple of vectors."""
    Ms = mat_mod(N)
    def act(g, B):
        return canon(tuple(tuple(int(x) for x in (np.array(v) @ Ms[g]) % N) for v in B))
    return orbit_action(canon(tuple(basis)), act)

def span_canon_p(p):
    def canon(B):
        # set of all vectors of span -> frozenset (small p only); an already-closed set maps elementwise
        if len(B) > 4: return frozenset(B)
        vs = set()
        B = [np.array(b) for b in B]
        for coeffs in itertools.product(range(p), repeat=len(B)):
            v = sum(c * b for c, b in zip(coeffs, B)) % p
            vs.add(tuple(int(x) for x in v))
        return frozenset(vs)
    return canon

def X_tuple(N, vecs):
    """ordered tuple of vectors (orbit of a frame)."""
    return X_subspace(N, vecs, lambda B: tuple(B))

def product_X(Xa, Xb):
    pa, _ = Xa; pb, _ = Xb
    return orbit_action((0, 0), lambda g, p: (int(pa[g][p[0]]), int(pb[g][p[1]])))

# ---------------- Schreier complex ----------------
def build_cells(perms):
    n = len(perms[0])
    inv = [np.argsort(p) for p in perms]
    rows, kap, names = [], [], []
    seen = set()
    for name, word in REL.items():
        k = KAP.get(name, 0)
        for x in range(n):
            row = {}
            cur = x; path = []
            for a in word:
                if a < 5:
                    e = a * n + cur; row[e] = row.get(e, 0) + 1; cur = perms[a][cur]
                else:
                    g = a - 5; cur = inv[g][cur]; e = g * n + cur; row[e] = row.get(e, 0) - 1
                path.append(cur)
            assert cur == x
            key = (k, tuple(sorted((e, c) for e, c in row.items() if c)))
            if key in seen: continue
            seen.add(key)
            rows.append({e: c for e, c in row.items() if c}); kap.append(k); names.append((name, x))
    m = len(rows)
    A = lil_matrix((m, 5 * n))
    for i, r in enumerate(rows):
        for e, c in r.items(): A[i, e] = c
    return csr_matrix(A), np.array(kap), names

# ---------------- LP with fixed rounding ----------------
def lp_fixed(A, c, nvec):
    """min eps s.t. |A th - c - n| <= eps ; returns eps, theta, dual cycle b (real)."""
    m, E = A.shape
    # vars: theta (E, free), eps
    one = csr_matrix(np.ones((m, 1)))
    Aub = vstack([hstack([A, -one]), hstack([-A, -one])]).tocsr()
    bub = np.concatenate([c + nvec, -(c + nvec)])
    cost = np.zeros(E + 1); cost[-1] = 1
    res = linprog(cost, A_ub=Aub, b_ub=bub, bounds=[(None, None)] * E + [(0, None)], method="highs")
    assert res.status == 0, res.message
    y = -res.ineqlin.marginals
    b = y[:m] - y[m:]
    return res.x[-1], res.x[:E], b

def alternate(A, c, theta0, iters=50):
    th = theta0; best = (9, None, None, None)
    for _ in range(iters):
        nvec = np.rint(A @ th - c)
        eps, th2, b = lp_fixed(A, c, nvec)
        if eps < best[0] - 1e-12: best = (eps, th2, b, nvec)
        else: break
        th = th2
    return best

def certificate(A, kap, b, maxden=10**6):
    """rationalize real dual cycle b, return exact lower bound dist(kappa(b)/3,Z)/||b||_1 if b integral cycle."""
    fr = [Fraction(float(x)).limit_denominator(maxden) for x in b]
    den = 1
    for f in fr: den = den * f.denominator // np.gcd(den, f.denominator)
    bi = np.array([int(f * den) for f in fr], dtype=object)
    g = 0
    for x in bi: g = np.gcd(g, int(x))
    if g: bi = bi // g
    # check cycle
    At = A.T.tocsr().astype(np.int64)
    chk = At @ np.array(bi, dtype=np.int64)
    if np.any(chk != 0): return None
    kb = int(sum(int(k) * int(x) for k, x in zip(kap, bi)))
    num = Fraction(kb, 3) - round(Fraction(kb, 3))
    l1 = int(sum(abs(int(x)) for x in bi))
    return abs(num) / l1, kb, l1

def mu_estimate(perms, restarts=20, seed=0, label=""):
    A, kap, names = build_cells(perms)
    c = kap / 3.0
    n = len(perms[0]); E = 5 * n
    rng = np.random.default_rng(seed)
    starts = [np.zeros(E)]
    # pullbacks of constant (point) solutions theta_g = t
    for t in np.linspace(0, 1, 7, endpoint=False)[1:]: starts.append(np.full(E, t))
    for _ in range(restarts): starts.append(rng.random(E))
    best = (9, None, None, None)
    for s in starts:
        r = alternate(A, c, s)
        if r[0] < best[0] - 1e-12: best = r
    eps, th, b, nvec = best
    cert = certificate(A, kap, b)
    return dict(label=label, npts=n, cells=A.shape[0], ub=eps, cert=None if cert is None else
                (str(cert[0]), float(cert[0]), cert[1], cert[2]))

def tree_edges(perms):
    """spanning tree of the Schreier graph (edge index g*n+x for edge x -> perms[g][x])."""
    n = len(perms[0]); seen = {0}; stack = [0]; T = []
    while stack:
        x = stack.pop()
        for g in range(5):
            for y, e in ((perms[g][x], g * n + x), (int(np.argsort(perms[g])[x]), None)):
                if e is None:
                    e = g * n + y
                if y not in seen:
                    seen.add(y); stack.append(y); T.append(e)
    assert len(seen) == n
    return T

def mu_milp(perms, time_limit=600, eps_cap=1 / 291 + 1e-7):
    A, kap, names = build_cells(perms)
    m, E = A.shape
    c = kap / 3.0
    T = set(tree_edges(perms))
    keep = [e for e in range(E) if e not in T]
    A = A[:, keep].tocsr(); E = len(keep)
    # vars: theta in [0,1] (E), n integer (m), eps ; residual A th - n - c in [-eps, eps]
    Apos = A.maximum(0); Aneg = (-A).maximum(0)
    nlo = np.floor(-np.array(Aneg.sum(axis=1)).ravel() - c - eps_cap)
    nhi = np.ceil(np.array(Apos.sum(axis=1)).ravel() - c + eps_cap)
    one = csr_matrix(np.ones((m, 1)))
    I = speye(m, format="csr")
    Aub = vstack([hstack([A, -I, -one]), hstack([-A, I, -one])]).tocsr()
    lo = np.full(2 * m, -np.inf); hi = np.concatenate([c, -c])
    cost = np.zeros(E + m + 1); cost[-1] = 1
    integ = np.concatenate([np.zeros(E), np.ones(m), [0]])
    lb = np.concatenate([np.zeros(E), nlo, [0]]); ub = np.concatenate([np.ones(E), nhi, [eps_cap]])
    res = milp(cost, constraints=LinearConstraint(Aub, lo, hi), integrality=integ, bounds=Bounds(lb, ub),
               options=dict(time_limit=time_limit, disp=False, mip_rel_gap=1e-9))
    return dict(status=res.status, msg=res.message, eps=None if res.x is None else res.x[-1],
                bound=getattr(res, "mip_dual_bound", None), cells=m)

def X_s6_tuples(k):
    """ordered k-tuples of distinct Weierstrass points; a_i acts by the transposition (i-1,i) (Birman-Hilden)."""
    def act(g, t):
        sw = {g: g + 1, g + 1: g}
        return tuple(sw.get(v, v) for v in t)
    return orbit_action(tuple(range(k)), act)

def X_s6_partition(blocks):
    """orbit of a set partition of {0..5} (blocks given as tuples), unordered blocks."""
    def act(g, P):
        sw = {g: g + 1, g + 1: g}
        return frozenset(frozenset(sw.get(v, v) for v in b) for b in P)
    return orbit_action(frozenset(frozenset(b) for b in blocks), act)

if __name__ == "__main__":
    pass
