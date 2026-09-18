#!/usr/bin/env python3
"""Floating-point scouting: infinite-volume Rayleigh quotient of the i.i.d. tree-stack ansatz.

Model (see forest_window_scout.py in ../thompson-f-cogrowth-2026-09-17/): an element of the set
Omega (trivial bottom forest) is a pointed forest; seen from the pointer it is a left stack, a
current tree and a right stack.  Palm ansatz: current tree ~ b, all other trees i.i.d. ~ a.
With x = sqrt(a), y = sqrt(b) (unit vectors) the per-site Rayleigh quotient of the adjacency
A = x0 + x0^-1 + x1 + x1^-1 is

    R(x, y) = 2 <x,y>^2 + 2 sum_{T=(L,R)} y(L) x(R) y(T).

Trees are truncated at N leaves.  Alternating maximisation.
"""
import sys
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh

N = int(sys.argv[1]) if len(sys.argv) > 1 else 9

trees = {1: [()]}
for n in range(2, N + 1):
    trees[n] = [(a, b) for k in range(1, n) for a in trees[k] for b in trees[n - k]]
allt = [t for n in range(1, N + 1) for t in trees[n]]
idx = {t: i for i, t in enumerate(allt)}
size = {t: n for n in trees for t in trees[n]}
D = len(allt)
triples = np.array([(idx[t], idx[t[0]], idx[t[1]]) for t in allt if t != ()])
TT, LL, RR = triples.T


def R(x, y):
    return 2 * (x @ y) ** 2 + 2 * np.sum(y[LL] * x[RR] * y[TT])


def best_y(x):
    M = coo_matrix((x[RR], (TT, LL)), shape=(D, D)).tocsr()
    Q = M + M.T
    # add rank one 2 x x^T via LinearOperator
    from scipy.sparse.linalg import LinearOperator
    op = LinearOperator((D, D), matvec=lambda v: Q @ v + 2 * x * (x @ v), dtype=float)
    w, v = eigsh(op, k=1, which='LA')
    v = np.abs(v[:, 0])
    return v / np.linalg.norm(v)


def best_x(y):
    v = np.zeros(D)
    np.add.at(v, RR, y[LL] * y[TT])
    best = (-1, None)
    for c in np.concatenate([np.linspace(0, 20, 401), [1e3]]):
        x = c * y + v
        x /= np.linalg.norm(x)
        r = R(x, y)
        if r > best[0]:
            best = (r, x)
    return best[1]


def main():
    rng = np.random.default_rng(0)
    beta = 0.3
    # start: critical-ish GW trees
    a = np.array([(0.5 ** (2 * size[t] - 1)) for t in allt])
    x = np.sqrt(a / a.sum())
    y = x.copy()
    for it in range(200):
        y = best_y(x)
        x = best_x(y)
    r = R(x, y)
    a, b = x ** 2, y ** 2
    ms = lambda p: sum(p[idx[t]] * size[t] for t in allt)
    print(f"N={N} trees={D} R={r:.6f} R/4={r/4:.6f} BC^2={(x@y)**2:.5f} "
          f"a(leaf)={a[0]:.4f} b(leaf)={b[0]:.4f} mean|a|={ms(a):.3f} mean|b|={ms(b):.3f} "
          f"mass(a,size=N)={sum(a[idx[t]] for t in trees[N]):.4f}")


if __name__ == "__main__":
    main()
