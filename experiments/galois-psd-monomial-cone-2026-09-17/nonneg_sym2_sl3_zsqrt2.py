#!/usr/bin/env python3
"""Nonnegative elements of H = Sym^2 SL_3(Z[sqrt2]) on Z^12.

Basis of Z^12: omega * v v^T, omega in {1, sqrt2}, v in V0 = {e1,e2,e3,e1+e2,e1+e3,e2+e3}.
A symmetric X over O = Z[sqrt2] has coordinates c_ij = X_ij (i<j), c_ii = X_ii - sum_{j!=i} X_ij,
and the Z-coordinates of c = a + b sqrt2 are (a, b).  sigma = Sym^2(g) is a nonnegative 12x12 matrix
iff every image omega (g v)(g v)^T has all coordinates a, b >= 0.

Checks:
 (1) BFS over words in elementary/diagonal generators of SL_3(O): every nonnegative element found
     lies in the predicted finite set  N_pred = { g in SL_3(Z) : columns and pairwise column sums in +-V0 }
     (in fact the nonnegative ones found are exactly the nonnegative members of N_pred).
 (2) The 12x12 matrices have determinant 1 (sampled), confirming H <= SL_12(Z).
 (3) The line in the closure K: u^(2n) E_11 and sqrt2 u^(2n) E_11 (u = 1+sqrt2, n -> -oo) lie in H . orthant
     and, normalised, converge to (0, +E_11) and (0, -E_11) in the (v_+, v_-) coordinates.
Run: nice -n 10 timeout 1200 python3 nonneg_sym2_sl3_zsqrt2.py
"""
import itertools, math
from fractions import Fraction

# elements of O as (a, b) = a + b sqrt2
def add(x, y): return (x[0] + y[0], x[1] + y[1])
def neg(x): return (-x[0], -x[1])
def mul(x, y): return (x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])
Z0, ONE, S2 = (0, 0), (1, 0), (0, 1)

def matmul(A, B):
    return tuple(tuple(
        (lambda acc: acc)(
            add(add(mul(A[i][0], B[0][j]), mul(A[i][1], B[1][j])), mul(A[i][2], B[2][j])))
        for j in range(3)) for i in range(3))

def ident():
    return tuple(tuple(ONE if i == j else Z0 for j in range(3)) for i in range(3))

V0 = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1)]
PAIRS = [(0, 1), (0, 2), (1, 2)]

def coords(X):
    """Coordinates of symmetric X (3x3 over O) in basis E_ii, P_ij."""
    out = []
    for i in range(3):
        c = X[i][i]
        for j in range(3):
            if j != i:
                c = add(c, neg(X[i][j]))
        out.append(c)
    for (i, j) in PAIRS:
        out.append(X[i][j])
    return out  # 6 elements of O

def image(g, v, omega):
    w = [add(add(mul(g[i][0], (v[0], 0)), mul(g[i][1], (v[1], 0))), mul(g[i][2], (v[2], 0))) for i in range(3)]
    X = [[mul(omega, mul(w[i], w[j])) for j in range(3)] for i in range(3)]
    return coords(X)

def sym2_matrix(g):
    cols = []
    for v in V0:
        for omega in (ONE, S2):
            c = image(g, v, omega)
            col = []
            for x in c:
                col += [x[0], x[1]]
            cols.append(col)
    # basis order: (v, omega) with coordinates (c_l, a/b); reorder rows to match (l, omega)
    # rows are indexed by (coordinate l in E11,E22,E33,P12,P13,P23 ; a or b)
    # columns by (v in V0 order E11,E22,E33,P12,P13,P23 ; omega) -- same order, so the matrix is square
    return [[cols[c][r] for c in range(12)] for r in range(12)]

def is_nonneg(g):
    for v in V0:
        for omega in (ONE, S2):
            for x in image(g, v, omega):
                if x[0] < 0 or x[1] < 0:
                    return False
    return True

def det_int(M):
    M = [[Fraction(x) for x in row] for row in M]
    n = len(M); d = Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None: return 0
        if p != c: M[c], M[p] = M[p], M[c]; d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if f:
                M[r] = [M[r][k] - f * M[c][k] for k in range(n)]
    return d

def elem(i, j, x):
    return tuple(tuple(ONE if a == b else (x if (a, b) == (i, j) else Z0) for b in range(3)) for a in range(3))

def diag(x, y, z):
    d = [x, y, z]
    return tuple(tuple(d[a] if a == b else Z0 for b in range(3)) for a in range(3))

U, UI = (1, 1), (-1, 1)  # 1+sqrt2 and its inverse sqrt2-1
gens = []
for i in range(3):
    for j in range(3):
        if i != j:
            for x in (ONE, neg(ONE), S2, neg(S2)):
                gens.append(elem(i, j, x))
for perm in itertools.permutations(range(3)):
    d = [ONE, ONE, ONE]
    d[perm[0]] = U; d[perm[1]] = UI
    gens.append(diag(*d))
# signed permutation matrices of determinant 1 (the predicted nonnegative elements live here)
for perm in itertools.permutations(range(3)):
    for signs in itertools.product((1, -1), repeat=3):
        P = [[0] * 3 for _ in range(3)]
        for c in range(3):
            P[perm[c]][c] = signs[c]
        det = (P[0][0] * (P[1][1] * P[2][2] - P[1][2] * P[2][1]) - P[0][1] * (P[1][0] * P[2][2] - P[1][2] * P[2][0])
               + P[0][2] * (P[1][0] * P[2][1] - P[1][1] * P[2][0]))
        if det == 1 and perm != (0, 1, 2) or (det == 1 and signs != (1, 1, 1)):
            gens.append(tuple(tuple((P[a][b], 0) for b in range(3)) for a in range(3)))

def predicted_set():
    signedV = [tuple(s * t for t in v) for v in V0 for s in (1, -1)]
    out = set()
    for c in itertools.product(signedV, repeat=3):
        g = tuple(tuple((c[j][i], 0) for j in range(3)) for i in range(3))
        # integer determinant
        a = [[c[j][i] for j in range(3)] for i in range(3)]
        det = (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1]) - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
               + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))
        if det != 1:
            continue
        ok = True
        for (i, j) in PAIRS:
            s = tuple(c[i][t] + c[j][t] for t in range(3))
            if s not in signedV:
                ok = False
        if ok:
            out.add(g)
    return out

def main():
    pred = predicted_set()
    pred_nonneg = {g for g in pred if is_nonneg(g)}
    print("predicted finite set N_pred:", len(pred), "  nonnegative members:", len(pred_nonneg))
    seen = {ident()}
    frontier = [ident()]
    import sys
    RADIUS = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    for r in range(RADIUS):
        nxt = []
        for g in frontier:
            for s in gens:
                h = matmul(g, s)
                if h not in seen:
                    seen.add(h); nxt.append(h)
        frontier = nxt
        print("radius", r + 1, "ball size", len(seen))
    found = {g for g in seen if is_nonneg(g)}
    print("nonnegative elements in ball:", len(found))
    print("all inside predicted set:", found <= pred_nonneg)
    for g in sorted(found):
        print("  ", [[x[0] + x[1] * math.sqrt(2) for x in row] for row in g])
    # determinant check on a sample
    sample = list(seen)[:200]
    print("det(Sym^2 g) == 1 on 200 samples:", all(det_int(sym2_matrix(g)) == 1 for g in sample))
    # line in the closure K
    lam = 3 + 2 * math.sqrt(2); lamc = 3 - 2 * math.sqrt(2)
    for n in (2, 5, 10):
        # u^(-2n) * E_11 and sqrt2 * u^(-2n) E_11 : (+,-) embeddings of the scalar, normalised by |.|
        for om, omc in ((1.0, 1.0), (math.sqrt(2), -math.sqrt(2))):
            vp, vm = om * lamc ** n, omc * lam ** n
            nrm = math.hypot(vp, vm)
            print(f"n={n} omega={om:.3f}: normalised (v_+, v_-) coefficient of E_11 = ({vp / nrm:.2e}, {vm / nrm:+.6f})")

if __name__ == "__main__":
    main()
