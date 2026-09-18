"""Exact infeasibility certificates for the lp5 certificate LP.

For a word w the LP  A y = b, y >= 0  (rows: darts d with b_d = 1, and antisymmetric
slot-pair rows with b = 0; columns: admissible vertex polygons) has no solution iff
there is z with  A^T z <= 0  and  b^T z > 0  (Farkas).  We compute z in floating point,
round it to rationals, and check both inequalities in exact integer arithmetic.  A word
whose certificate verifies admits no legal f-folded fatgraph with boundary d^- = N
copies of w and d^+ = N copies of f(w)^{-1}, for any N (see the -proof note).

usage: python3 exact_farkas.py '<phi json>' m maxlen maxdarts out.log [words...]
"""
import sys, json, time
from fractions import Fraction
from math import lcm
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from ffold import *
from search3 import power
from search2 import legal_words_dfs
from lp5 import polygons


def rows_of(B, polys):
    N = B.N; pairs = {}; cols = []
    for P in polys:
        col = {}
        for (d, q) in P:
            col[d] = col.get(d, 0) + 1
            key = (min(d, q), max(d, q))
            r = pairs.setdefault(key, N + len(pairs))
            col[r] = col.get(r, 0) + (1 if d < q else -1)
        cols.append(col)
    return N + len(pairs), cols


def exact_check(N, cols, z):
    """z: dict row -> int.  Returns True iff A^T z <= 0 and b^T z > 0 exactly."""
    if sum(z.get(d, 0) for d in range(N)) <= 0:
        return False
    return all(sum(c * z.get(r, 0) for r, c in col.items()) <= 0 for col in cols)


def certify(phi, g, w, maxval):
    B = Boundary(phi, [w])
    polys = polygons(B, g, maxval)
    nrows, cols = rows_of(B, polys)
    used = {d for P in polys for (d, q) in P}
    free = [d for d in range(B.N) if d not in used]
    if free:                                   # a dart lying in no admissible polygon
        z = {free[0]: 1}
        return ("uncovered-dart", exact_check(B.N, cols, z))
    r, c, v = [], [], []
    for j, col in enumerate(cols):
        for row, val in col.items():
            r.append(j); c.append(row); v.append(float(val))
    AT = coo_matrix((v, (r, c)), shape=(len(cols), nrows)).tocsr()
    bvec = np.zeros(nrows); bvec[:B.N] = 1.0
    res = linprog(np.zeros(nrows), A_ub=AT, b_ub=np.zeros(len(cols)),
                  A_eq=bvec.reshape(1, -1), b_eq=[1.0], bounds=(-1, 1), method="highs")
    if res.status != 0:
        return ("lp-feasible", False)
    for den in (1, 2, 4, 8, 16, 64, 256, 1024, 10 ** 6):
        fr = [Fraction(x).limit_denominator(den) for x in res.x]
        L = 1
        for x in fr: L = lcm(L, x.denominator)
        z = {i: int(x * L) for i, x in enumerate(fr) if x != 0}
        if exact_check(B.N, cols, z):
            return ("farkas", True)
    for tol in (1e-7, 1e-5, 1e-9, 1e-4):
        for den in (64, 0, 10 ** 4):
            z = exact_active_set(B.N, nrows, cols, res.x, AT, tol, den)
            if z is not None and exact_check(B.N, cols, z):
                return ("farkas-active-set", True)
    return ("farkas-rounding-failed", False)


def exact_active_set(N, nrows, cols, x, AT, tol=1e-7, den=64):
    """Snap a floating Farkas vector onto its active face exactly (python-flint).

    Equalities: (A^T z)_j = 0 for every column j that is tight at x, and b^T z = 1.
    Free variables of the reduced row echelon form take x rounded to small rationals;
    pivot variables are then determined exactly.  The caller re-checks every
    inequality in exact arithmetic, so this is only a way of producing a candidate."""
    import flint
    s = AT @ x
    act = [j for j in range(len(cols)) if s[j] > -tol]
    rows = []
    for j in act:
        r = [0] * (nrows + 1)
        for row, val in cols[j].items(): r[row] = val
        rows.append(r)
    rows.append([1] * N + [0] * (nrows - N) + [1])
    M = flint.fmpq_mat(len(rows), nrows + 1, [v for r in rows for v in r])
    R, rank = M.rref()
    piv = []
    for i in range(rank):
        c = next(c for c in range(nrows + 1) if R[i, c] != 0)
        piv.append(c)
    if nrows in piv:
        return None                          # inconsistent face
    pset = set(piv)
    val = [None] * nrows
    for c in range(nrows):
        if c not in pset:
            fr = Fraction(float(x[c])).limit_denominator(den) if den else Fraction(0)
            val[c] = flint.fmpq(fr.numerator, fr.denominator)
    for i, c in enumerate(piv):
        t = R[i, nrows]
        for c2 in range(nrows):
            if c2 not in pset and R[i, c2] != 0:
                t -= R[i, c2] * val[c2]
        val[c] = t
    L = 1
    for v in val: L = lcm(L, int(v.q))
    return {i: int(v * L) for i, v in enumerate(val) if v != 0}


def main(phi0, m, maxlen, maxdarts, out, words=None):
    phi = power(phi0, m); g = gate_of(phi)
    gp = len({g[d] for d in "abc"}); gn = len({g[d] for d in "ABC"})
    maxval = max(2, 2 * min(gp, gn))
    if words is None:
        words = sorted(legal_words_dfs(g, maxlen, True), key=lambda w: (len(w), w))
    words = [w for w in words if len(w) + len(apply(phi, w)) <= maxdarts]
    stats = {}; bad = []
    t0 = time.time()
    with open(out, "w") as fh:
        fh.write(f"phi0 {phi0} m {m} phi {phi} gates {''.join(g[d] for d in 'abcABC')} maxval {maxval} "
                 f"words {len(words)} (all legal primitive zero-homology cyclic words, len<={maxlen}, "
                 f"|w|+|f(w)|<={maxdarts})\n")
        for w in words:
            kind, ok = certify(phi, g, w, maxval)
            stats[(kind, ok)] = stats.get((kind, ok), 0) + 1
            if not ok:
                bad.append((w, kind)); fh.write(f"NOT CERTIFIED {w} {kind}\n")
            fh.write(f"done {w} {kind}\n"); fh.flush()
        fh.write(f"stats {stats} time {round(time.time() - t0, 1)}\n")
    print(open(out).read()[-600:])


if __name__ == "__main__":
    main(json.loads(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5],
         sys.argv[6:] or None)
