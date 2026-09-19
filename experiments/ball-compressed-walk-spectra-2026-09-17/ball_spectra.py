"""Ball-compressed return eigenvalues of the lazy walk.

For a group G with symmetric generating set S, let S' = S u {e}, P = |S'|^-1 sum_{s in S'} lambda_s and
Q = (I + P)/2 (positive semidefinite, supported on B_1).  For n, t >= 0 put

    rho(n, t) = max { <eta, Q^t eta> : eta in l2(B_n), ||eta|| = 1 }

(the top eigenvalue of Q^t compressed to l2(B_n)), and

    h(N) = min { n : rho(n, N) >= 1/2 }.

The node coarse-reiter-radius-is-a-ball-compressed-return-radius proves h(N) <= CR(N) and
CR(N) <= h(2J) + J with J = ceil(16 |S'| N^2 ln 2).

This script computes rho(n, t) exactly up to floating point (Lanczos on the operator
eta -> Pi_n Q^t Pi_n eta, which only needs the ball B_{n + t}) for
  * Thompson's F with S = {x0, x1}^{+-1}, elements as exact PL maps with Fraction breakpoints;
  * the free group F_2 = <a, b> as calibration (reduced words).

Usage: python3 ball_spectra.py F 9 12     (group, max radius R, max time T with n + T <= R)
Output: JSON on stdout.
"""
import json
import sys
from fractions import Fraction as Fr

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import LinearOperator, eigsh

# ---------------- Thompson's F as PL maps ----------------


def canon(bps):
    """Drop collinear breakpoints; bps is a tuple of (x, y) with x increasing, (0,0) .. (1,1)."""
    out = [bps[0]]
    for i in range(1, len(bps) - 1):
        (xa, ya), (xb, yb), (xc, yc) = out[-1], bps[i], bps[i + 1]
        if (yb - ya) * (xc - xb) != (yc - yb) * (xb - xa):
            out.append(bps[i])
    out.append(bps[-1])
    return tuple(out)


def evaluate(f, x):
    for (xa, ya), (xb, yb) in zip(f, f[1:]):
        if xa <= x <= xb:
            return ya + (yb - ya) * (x - xa) / (xb - xa)
    raise ValueError(x)


def inverse(f):
    return tuple((y, x) for (x, y) in f)


def compose(f, g):
    """(f o g)(x) = f(g(x))."""
    ginv = inverse(g)
    xs = set(x for x, _ in g) | set(evaluate(ginv, y) for y, _ in ((p[0], None) for p in f))
    xs = sorted(xs)
    return canon(tuple((x, evaluate(f, evaluate(g, x))) for x in xs))


X0 = canon(((Fr(0), Fr(0)), (Fr(1, 2), Fr(1, 4)), (Fr(3, 4), Fr(1, 2)), (Fr(1), Fr(1))))
X1 = canon(((Fr(0), Fr(0)), (Fr(1, 2), Fr(1, 2)), (Fr(3, 4), Fr(5, 8)), (Fr(7, 8), Fr(3, 4)), (Fr(1), Fr(1))))
ID_F = ((Fr(0), Fr(0)), (Fr(1), Fr(1)))
GENS_F = [X0, inverse(X0), X1, inverse(X1)]

# ---------------- free group F_2 as reduced words ----------------
INV = {"a": "A", "A": "a", "b": "B", "B": "b"}
GENS_W = ["a", "A", "b", "B"]


def wmul(s, w):
    if w and w[0] == INV[s]:
        return w[1:]
    return s + w


def ball(group, R):
    if group == "F":
        ident, gens, mul = ID_F, GENS_F, lambda s, x: compose(s, x)
    else:
        ident, gens, mul = "", GENS_W, wmul
    index = {ident: 0}
    radius = [0]
    frontier = [ident]
    for r in range(1, R + 1):
        nxt = []
        for x in frontier:
            for s in gens:
                y = mul(s, x)
                if y not in index:
                    index[y] = len(radius)
                    radius.append(r)
                    nxt.append(y)
        frontier = nxt
    elems = [None] * len(index)
    for k, i in index.items():
        elems[i] = k
    # left-multiplication adjacency inside B_R (neighbours outside B_R are never reached by Q^t eta, see docstring)
    rows, cols = [], []
    for i, x in enumerate(elems):
        if radius[i] == R:
            continue
        for s in gens:
            rows.append(i)
            cols.append(index[mul(s, x)])
    radius = np.array(radius)
    return elems, radius, rows, cols


def main():
    group, R, T = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    elems, radius, rows, cols = ball(group, R)
    Nb = len(elems)
    A = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(Nb, Nb))
    deg = 5.0  # |S'| = 5 for both groups

    def Q(v):
        # (P v)(x) = (1/5)(v(x) + sum_s v(s^-1 x)); adjacency is symmetric on the interior.
        return 0.5 * v + 0.5 * (v + A.T @ v) / deg

    sizes = [int((radius <= r).sum()) for r in range(R + 1)]
    table = {}
    for t in range(1, T + 1):
        for n in range(0, R - t + 1):
            mask = radius <= n
            m = int(mask.sum())
            idx = np.nonzero(mask)[0]

            def op(u, idx=idx, t=t):
                v = np.zeros(Nb)
                v[idx] = u
                for _ in range(t):
                    v = Q(v)
                return v[idx]

            if m == 1:
                lam = float(op(np.ones(1))[0])
            else:
                L = LinearOperator((m, m), matvec=op, dtype=float)
                lam = float(eigsh(L, k=1, which="LA", tol=1e-10)[0][0])
            table[f"{n},{t}"] = lam
    h = {}
    for t in range(1, T + 1):
        ok = [n for n in range(0, R - t + 1) if table[f"{n},{t}"] >= 0.5]
        h[t] = min(ok) if ok else None
    print(json.dumps({"group": group, "R": R, "T": T, "ball_sizes": sizes, "rho": table, "h": h}, indent=1))


if __name__ == "__main__":
    main()
