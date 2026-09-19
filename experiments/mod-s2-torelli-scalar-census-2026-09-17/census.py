#!/usr/bin/env python3
"""Monomial Torelli-scalar census for Mod(S_2).

For a finite-index subgroup Gamma' of Sp_4(Z), given as the stabilizer of an
object under a right action of Sp_4(Z/N), let M' = pi^{-1}(Gamma') in
M = Mod(S_2).  For a character psi of M', the induced representation
Ind_{M'}^M psi is diagonal on the separating twist t_s = (a1 a2)^6 (t_s lies in
the Torelli group K, which is normal and contained in M'), with eigenvalues
psi(g_c t_s g_c^{-1}) over the cosets c.

Let v_c be the class of g_c t_s g_c^{-1} in H_1(M'), and
W = ker(Z^{cosets} -> H_1(M'), e_c -> v_c).  The eigenvalue vectors of the
monomial representations are exactly the h in (R/Z)^{cosets} with h.W = 0, so

    d(Gamma') = min_{psi} || Ind psi(t_s) - omega I ||  (angle / 2 pi)
              = dist_inf( (1/3) 1 , W^perp )            in (R/Z)^{classes}.

A w in W with aug(w) not divisible by 3 certifies
    d(Gamma') >= || aug(w)/3 ||_{R/Z} / ||w||_1 .

Requirements: python-flint (fmpz_mat.hnf), numpy, scipy (milp).
Usage:  python3 census.py [case ...]      (no argument: all default cases)
"""
import itertools
import json
import sys
import time

import numpy as np
from flint import fmpz_mat

# ---------------------------------------------------------------------------
# 1. Birman--Hilden presentation of M = Mod(S_2) on the Humphries chain a1..a5.
#    Letters are 0..4 (positive generators only; every relator is u = v with
#    u, v positive words).
# ---------------------------------------------------------------------------
NGEN = 5
IOTA = [0, 1, 2, 3, 4, 4, 3, 2, 1, 0]          # hyperelliptic involution
T_S = [0, 1] * 6                               # separating twist (a1 a2)^6


def relators():
    rels = []
    for i in range(NGEN - 1):                  # braid relations
        rels.append(([i, i + 1, i], [i + 1, i, i + 1]))
    for i in range(NGEN):                      # far commutation
        for j in range(i + 2, NGEN):
            rels.append(([i, j], [j, i]))
    rels.append(([0, 1, 2, 3, 4] * 6, []))     # (a1..a5)^6 = 1
    rels.append((IOTA + IOTA, []))             # iota^2 = 1
    for i in range(NGEN):                      # iota central
        rels.append((IOTA + [i], [i] + IOTA))
    return rels


# ---------------------------------------------------------------------------
# 2. Symplectic representation.  Basis (a1, b1, a2, b2), <a_i, b_i> = 1.
#    Chain classes x1..x5 = b1, a1, b1+b2, a2, b2.  Twist matrix acts on
#    column vectors by v -> v + <x, v> x; objects are acted on the right by
#    row vectors o -> o A, which is a right action of the matrix group.
# ---------------------------------------------------------------------------
J = np.array([[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 1], [0, 0, -1, 0]],
             dtype=np.int64)
CHAIN = [np.array(v, dtype=np.int64) for v in
         ([0, 1, 0, 0], [1, 0, 0, 0], [0, 1, 0, 1], [0, 0, 1, 0],
          [0, 0, 0, 1])]


def transvection(x):
    # v -> v + (x^T J v) x  as a matrix acting on column vectors
    return np.eye(4, dtype=np.int64) + np.outer(x, x @ J)


GENMATS = [transvection(x) for x in CHAIN]


def word_matrix(word):
    A = np.eye(4, dtype=np.int64)
    for letter in word:
        A = A @ GENMATS[letter]
    return A


def check_symplectic_rep():
    I4 = np.eye(4, dtype=np.int64)
    for A in GENMATS:
        assert (A.T @ J @ A == J).all()
    for u, v in relators():
        assert (word_matrix(u) == word_matrix(v)).all(), (u, v)
    assert (word_matrix(IOTA) == -I4).all()
    assert (word_matrix(T_S) == I4).all()
    return True


# ---------------------------------------------------------------------------
# 3. Finite objects with a right Sp_4(Z/N) action, and coset enumeration.
#    An object is an (m x 4) integer matrix mod N; `canon` picks a canonical
#    representative of its class.  The stabilizer of o0 is Gamma'.
# ---------------------------------------------------------------------------
def rref_mod_p(rows, p):
    A = [list(map(lambda t: int(t) % p, r)) for r in rows]
    m = len(A)
    piv_row = 0
    for col in range(4):
        pr = None
        for r in range(piv_row, m):
            if A[r][col] % p:
                pr = r
                break
        if pr is None:
            continue
        A[piv_row], A[pr] = A[pr], A[piv_row]
        inv = pow(A[piv_row][col], -1, p)
        A[piv_row] = [(t * inv) % p for t in A[piv_row]]
        for r in range(m):
            if r != piv_row and A[r][col]:
                f = A[r][col]
                A[r] = [(a - f * b) % p for a, b in zip(A[r], A[piv_row])]
        piv_row += 1
    return tuple(tuple(r) for r in A[:piv_row])


def canon_subspace(p):
    return lambda rows: rref_mod_p(rows, p)


def canon_vectors_up_to(N, units):
    def canon(rows):
        best = None
        for u in units:
            cand = tuple(tuple((u * int(t)) % N for t in r) for r in rows)
            if best is None or cand < best:
                best = cand
        return best
    return canon


def canon_exact(N):
    return lambda rows: tuple(tuple(int(t) % N for t in r) for r in rows)


def canon_tuple_of(canons, sizes):
    """Object = concatenation of several blocks, each canonicalised."""
    def canon(rows):
        out, k = [], 0
        for c, s in zip(canons, sizes):
            out.append(c(rows[k:k + s]))
            k += s
        return tuple(out)
    return canon


def enumerate_cosets(o0, N, canon, limit=20000):
    mats = [A % N for A in GENMATS]
    start = canon(np.array(o0, dtype=np.int64))
    index = {start: 0}
    objs = [start]
    act = []
    q = 0
    while q < len(objs):
        o = objs[q]
        arr = np.array(unflatten(o), dtype=np.int64)
        row = []
        for A in mats:
            nb = canon((arr @ A) % N)
            if nb not in index:
                index[nb] = len(objs)
                objs.append(nb)
                if len(objs) > limit:
                    raise RuntimeError("orbit exceeds limit")
            row.append(index[nb])
        act.append(row)
        q += 1
    return objs, act


def unflatten(o):
    """Turn a canonical object (possibly nested tuple of blocks) into rows."""
    if len(o) and isinstance(o[0], tuple) and len(o[0]) and \
            isinstance(o[0][0], tuple):
        rows = []
        for block in o:
            rows.extend(block)
        return rows
    return list(o)


def trace_perm(act, c, word):
    for letter in word:
        c = act[c][letter]
    return c


def check_action(act):
    k = len(act)
    for u, v in relators():
        for c in range(k):
            assert trace_perm(act, c, u) == trace_perm(act, c, v)
    for c in range(k):
        assert trace_perm(act, c, T_S) == c
    return True


# ---------------------------------------------------------------------------
# 4. Abelianised Reidemeister--Schreier for M' = Stab(coset 0).
# ---------------------------------------------------------------------------
def schreier(act):
    k = len(act)
    seen = [False] * k
    seen[0] = True
    tree = set()
    queue = [0]
    for c in queue:
        for i in range(NGEN):
            d = act[c][i]
            if not seen[d]:
                seen[d] = True
                tree.add((c, i))
                queue.append(d)
    assert all(seen)
    gen = {}
    for c in range(k):
        for i in range(NGEN):
            if (c, i) not in tree:
                gen[(c, i)] = len(gen)
    return gen


def trace_word(act, gen, c, word, vec):
    for letter in word:
        g = gen.get((c, letter))
        if g is not None:
            vec[g] = vec.get(g, 0) + 1
        c = act[c][letter]
    return c


def rs_data(act):
    gen = schreier(act)
    k = len(act)
    rels = []
    for u, v in relators():
        for c in range(k):
            vec = {}
            e1 = trace_word(act, gen, c, u, vec)
            neg = {}
            e2 = trace_word(act, gen, c, v, neg)
            assert e1 == e2
            for g, a in neg.items():
                vec[g] = vec.get(g, 0) - a
            vec = {g: a for g, a in vec.items() if a}
            if vec:
                rels.append(vec)
    vs = []
    for c in range(k):
        vec = {}
        e = trace_word(act, gen, c, T_S, vec)
        assert e == c
        vs.append({g: a for g, a in vec.items() if a})
    return len(gen), rels, vs


def unit_eliminate(ngen, rels, vs):
    """Exact Z-elimination of generators through relators with a +-1 entry.
    Returns the surviving generator list, relators and target vectors."""
    rows = {r: dict(v) for r, v in enumerate(rels)}
    colrows = {}
    for r, v in rows.items():
        for g in v:
            colrows.setdefault(g, set()).add(r)
    vrows = [dict(v) for v in vs]
    vcol = {}
    for t, v in enumerate(vrows):
        for g in v:
            vcol.setdefault(g, set()).add(t)
    alive_cols = set(range(ngen))
    progress = True
    while progress:
        progress = False
        order = sorted(rows, key=lambda r: len(rows[r]))
        for r in order:
            if r not in rows:
                continue
            v = rows[r]
            if not v:
                del rows[r]
                continue
            units = [g for g, a in v.items() if a in (1, -1)]
            if not units:
                continue
            j = min(units, key=lambda g: len(colrows.get(g, ())))
            s = v[j]
            piv = dict(v)
            # remove pivot row
            del rows[r]
            for g in piv:
                colrows[g].discard(r)
            for q in list(colrows.get(j, ())):
                a = rows[q][j]
                f = a * s
                row = rows[q]
                for g, b in piv.items():
                    nv = row.get(g, 0) - f * b
                    if nv:
                        if g not in row:
                            colrows.setdefault(g, set()).add(q)
                        row[g] = nv
                    elif g in row:
                        del row[g]
                        colrows[g].discard(q)
            for t in list(vcol.get(j, ())):
                a = vrows[t][j]
                f = a * s
                row = vrows[t]
                for g, b in piv.items():
                    nv = row.get(g, 0) - f * b
                    if nv:
                        if g not in row:
                            vcol.setdefault(g, set()).add(t)
                        row[g] = nv
                    elif g in row:
                        del row[g]
                        vcol[g].discard(t)
            alive_cols.discard(j)
            colrows.pop(j, None)
            vcol.pop(j, None)
            progress = True
    cols = sorted(alive_cols)
    return cols, [v for v in rows.values() if v], vrows


# ---------------------------------------------------------------------------
# 5. Lattices: H_1(M') = Z^cols / R, classes of the v_c, and W.
# ---------------------------------------------------------------------------
def to_dense(dicts, cols):
    pos = {g: i for i, g in enumerate(cols)}
    out = []
    for v in dicts:
        row = [0] * len(cols)
        for g, a in v.items():
            row[pos[g]] = a
        out.append(row)
    return out


def hnf_rows(rows, ncols):
    if not rows:
        return []
    H = fmpz_mat(rows).hnf()
    out = []
    for i in range(H.nrows()):
        r = [int(H[i, j]) for j in range(ncols)]
        if any(r):
            out.append(r)
    return out


def reduce_mod_hnf(x, H):
    x = list(x)
    for r in H:
        p = next(j for j, a in enumerate(r) if a)
        q = x[p] // r[p]
        if q:
            x = [a - q * b for a, b in zip(x, r)]
    return tuple(x)


def h1_invariants(R, ncols):
    if not R:
        return ncols, []
    D = fmpz_mat(R).snf()
    diag = [abs(int(D[i, i])) for i in range(min(D.nrows(), D.ncols()))]
    nz = [d for d in diag if d]
    return ncols - len(nz), [d for d in nz if d != 1]


def w_lattice(R, V, ncols):
    """Basis (HNF rows) of W = {w : sum w_c V_c in rowspace(R)}."""
    m = len(V)
    big = [list(r) + [0] * m for r in R]
    for c, v in enumerate(V):
        e = [0] * m
        e[c] = 1
        big.append(list(v) + e)
    H = hnf_rows(big, ncols + m)
    return [r[ncols:] for r in H if not any(r[:ncols])]


# ---------------------------------------------------------------------------
# 6. Distance d = dist_inf((1/3)1, W^perp) and l1 certificates.
#    W^perp lifted to R^m is {h : B h in Z^r}, B a basis of W.
# ---------------------------------------------------------------------------
def distance_milp(B, target=1.0 / 3.0):
    """min t s.t. B h = n (n integer), |h_j - target| <= t."""
    from scipy.optimize import Bounds, LinearConstraint, milp
    Bf = np.array(B, dtype=float)
    r, m = Bf.shape
    nv = m + r + 1                              # h, n, t
    c = np.zeros(nv)
    c[-1] = 1.0
    A_eq = np.hstack([Bf, -np.eye(r), np.zeros((r, 1))])
    A1 = np.hstack([np.eye(m), np.zeros((m, r)), -np.ones((m, 1))])
    A2 = np.hstack([-np.eye(m), np.zeros((m, r)), -np.ones((m, 1))])
    cons = [LinearConstraint(A_eq, 0, 0),
            LinearConstraint(A1, -np.inf, target),
            LinearConstraint(A2, -np.inf, -target)]
    integrality = np.concatenate([np.zeros(m), np.ones(r), np.zeros(1)])
    lb = np.concatenate([np.full(m, target - 0.5), np.full(r, -1e7), [0]])
    ub = np.concatenate([np.full(m, target + 0.5), np.full(r, 1e7), [0.5]])
    res = milp(c, constraints=cons, integrality=integrality,
               bounds=Bounds(lb, ub), options={"time_limit": 900})
    if res.x is None:
        return None
    n = [int(round(v)) for v in res.x[m:m + r]]
    return exact_point(B, n, res.x[:m], target)


def exact_point(B, n, h0, target):
    """Project h0 exactly (over Q) onto {h : B h = n}; return exact distance."""
    from fractions import Fraction
    import sympy
    Bs = sympy.Matrix(B)
    h0s = sympy.Matrix([sympy.Rational(Fraction(float(v)).limit_denominator(10**6))
                        for v in h0])
    ns = sympy.Matrix(n)
    G = Bs * Bs.T
    corr = Bs.T * G.solve(ns - Bs * h0s)
    h = h0s + corr
    assert Bs * h == ns
    t = sympy.Rational(1, 3) if target == 1.0 / 3.0 else sympy.nsimplify(target)
    dev = max(abs(v - t) for v in h)
    return dev, [str(v) for v in h]


def best_certificate(B):
    """min ||w||_1 over w in W with aug(w) = 3q + 1 (w -> -w covers 2 mod 3).
    Gives the rigorous bound d >= (1/3)/||w||_1."""
    from scipy.optimize import Bounds, LinearConstraint, milp
    Bf = np.array(B, dtype=float)
    r, m = Bf.shape
    nv = r + 1 + m                              # y, q, p >= |w|
    c = np.concatenate([np.zeros(r + 1), np.ones(m)])
    aug = Bf.sum(axis=1)
    A_aug = np.concatenate([aug, [-3.0], np.zeros(m)])[None, :]
    A1 = np.hstack([Bf.T, np.zeros((m, 1)), -np.eye(m)])
    A2 = np.hstack([-Bf.T, np.zeros((m, 1)), -np.eye(m)])
    cons = [LinearConstraint(A_aug, 1, 1),
            LinearConstraint(A1, -np.inf, 0),
            LinearConstraint(A2, -np.inf, 0)]
    integrality = np.concatenate([np.ones(r + 1), np.zeros(m)])
    lb = np.concatenate([np.full(r + 1, -1e6), np.zeros(m)])
    ub = np.concatenate([np.full(r + 1, 1e6), np.full(m, np.inf)])
    res = milp(c, constraints=cons, integrality=integrality,
               bounds=Bounds(lb, ub), options={"time_limit": 900})
    if res.x is None:
        return None, None
    y = [int(round(v)) for v in res.x[:r]]
    w = [sum(B[i][j] * y[i] for i in range(r)) for j in range(m)]
    assert sum(w) % 3 != 0
    return sum(abs(a) for a in w), w


# ---------------------------------------------------------------------------
# 7. Cases.  Each case yields (start object, step function).
# ---------------------------------------------------------------------------
def enumerate_by_step(start, step, limit=60000):
    index = {start: 0}
    objs = [start]
    act = []
    q = 0
    while q < len(objs):
        row = []
        for i in range(NGEN):
            nb = step(objs[q], i)
            if nb not in index:
                index[nb] = len(objs)
                objs.append(nb)
                if len(objs) > limit:
                    raise RuntimeError("orbit exceeds limit")
            row.append(index[nb])
        act.append(row)
        q += 1
    return objs, act


def matrix_case(rows, N, canon):
    mats = [A % N for A in GENMATS]
    start = canon(np.array(rows, dtype=np.int64))

    def step(o, i):
        return canon((np.array(unflatten(o), dtype=np.int64) @ mats[i]) % N)
    return start, step


def quad_case(odd):
    """Quadratic forms on F_2^4 polarising to J; right action q -> q o A."""
    Jl = J % 2

    def qval(q, v):
        s = sum(int(c) * q[i] for i, c in enumerate(v))
        for i in range(4):
            for j in range(i + 1, 4):
                s += int(v[i]) * int(v[j]) * int(Jl[i, j])
        return s % 2

    def arf(q):
        # symplectic basis (a1,b1,a2,b2) = (e0,e1,e2,e3)
        return (q[0] * q[1] + q[2] * q[3]) % 2

    start = (1, 1, 0, 0) if odd else (0, 0, 0, 0)
    assert arf(start) == (1 if odd else 0)
    mats = [A % 2 for A in GENMATS]

    def step(q, i):
        A = mats[i]
        return tuple(qval(q, A[:, k]) for k in range(4))
    return start, step


def case(name):
    e = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
    if "+" in name:                          # intersection of stabilizers
        parts = [case(nm) for nm in name.split("+")]
        start = tuple(s for s, _ in parts)

        def step(o, i):
            return tuple(st(oj, i) for (_, st), oj in zip(parts, o))
        return start, step
    if name == "sp4":
        return matrix_case([[0, 0, 0, 0]], 1, canon_exact(1))
    if name == "theta-odd":
        return quad_case(True)
    if name == "theta-even":
        return quad_case(False)
    kind, p = name.rsplit("-", 1)
    p = int(p)
    if kind == "pt":
        return matrix_case([e[0]], p, canon_subspace(p))
    if kind == "lag":
        return matrix_case([e[0], e[2]], p, canon_subspace(p))
    if kind == "plane":
        return matrix_case([e[0], e[1]], p, canon_subspace(p))
    if kind == "flag":
        c = canon_tuple_of([canon_subspace(p), canon_subspace(p)], [1, 2])
        return matrix_case([e[0], e[0], e[2]], p, c)
    if kind == "vec":
        return matrix_case([e[0]], p, canon_exact(p))
    if kind == "vecpm":
        return matrix_case([e[0]], p, canon_vectors_up_to(p, [1, p - 1]))
    if kind == "line":                       # primitive vectors mod units
        units = [u for u in range(1, p) if np.gcd(u, p) == 1]
        return matrix_case([e[0]], p, canon_vectors_up_to(p, units))
    if kind == "framepm":                    # Gamma(N) . {+-1}
        return matrix_case(e, p, canon_vectors_up_to(p, [1, p - 1]))
    if kind == "frame":
        return matrix_case(e, p, canon_exact(p))
    raise ValueError(name)


DEFAULT = ["sp4", "theta-odd", "theta-even", "pt-2", "lag-2", "plane-2",
           "flag-2", "pt-3", "lag-3", "vec-3", "plane-3", "flag-3", "pt-5",
           "lag-5", "vecpm-4"]


def run(name, do_milp=True):
    t0 = time.time()
    start, step = case(name)
    objs, act = enumerate_by_step(start, step)
    check_action(act)
    k = len(act)
    ngen, rels, vs = rs_data(act)
    cols, R, V = unit_eliminate(ngen, rels, vs)
    Rd = to_dense(R, cols)
    Vd = to_dense(V, cols)
    H = hnf_rows(Rd, len(cols)) if Rd else []
    b1, tors = h1_invariants(H, len(cols)) if H else (len(cols), [])
    classes = {}
    cls_of = []
    for c in range(k):
        key = reduce_mod_hnf(Vd[c], H)
        if key not in classes:
            classes[key] = len(classes)
        cls_of.append(classes[key])
    reps = [None] * len(classes)
    mult = [0] * len(classes)
    for c in range(k):
        if reps[cls_of[c]] is None:
            reps[cls_of[c]] = c
        mult[cls_of[c]] += 1
    Vr = [Vd[c] for c in reps]
    B = w_lattice(H, Vr, len(cols))
    m = len(reps)
    r = len(B)
    augs = [sum(row) for row in B]
    g = 0
    for a in augs:
        g = int(np.gcd(g, a))
    out = {
        "case": name, "index": k, "schreier_gens": ngen,
        "gens_after_unit_elim": len(cols), "b1": b1, "torsion": tors,
        "classes": m, "class_multiplicities": sorted(mult),
        "rank_W": r, "rank_image_of_K_in_H1": m - r,
        "gcd_aug_W": g,
        "deligne_ok": any(a % 3 for a in augs),
        "W_basis": B,
        "class_rep_objects": [objs[c] for c in reps],
        "coset_class": cls_of if k <= 60000 else None,
    }
    if do_milp and r:
        cert = best_certificate(B)
        out["cert_l1"], out["cert_w"] = cert
        if cert[0]:
            out["lower_bound"] = f"1/(3*{cert[0]})"
        dist = distance_milp(B)
        if dist is not None:
            out["distance"] = str(dist[0])
            out["distance_float"] = float(dist[0])
            out["optimal_h"] = dist[1]
    out["seconds"] = round(time.time() - t0, 1)
    return out


def main(argv):
    check_symplectic_rep()
    names = argv or DEFAULT
    results = []
    for name in names:
        res = run(name)
        results.append(res)
        short = {kk: vv for kk, vv in res.items()
                 if kk not in ("W_basis", "optimal_h", "cert_w",
                                   "class_rep_objects", "coset_class")}
        print(json.dumps(short), flush=True)
    return results


if __name__ == "__main__":
    import os
    res = main(sys.argv[1:])
    here = os.path.dirname(os.path.abspath(__file__))
    fname = ("census-results.json" if len(sys.argv) < 2 else
             "census-results-" + "_".join(sys.argv[1:]) + ".json")
    with open(os.path.join(here, fname), "w") as f:
        json.dump(res, f, indent=1)
