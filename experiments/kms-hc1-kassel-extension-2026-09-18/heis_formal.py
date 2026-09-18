"""Edge-compatible formality of the Heisenberg group algebra F_p[U], U = <a,b | a^p,b^p,[a,b,a],[a,b,b]>.

u = u(heis) = F_p<X,Y>/(X^p, Y^p, [[X,Y],X], [[X,Y],Y]), PBW basis X^i Y^j Z^k (Z = XY - YX central, Z^p = 0).
For A = 1 + f(X), B = 1 + g(Y) with f = X + f2 X^2 + ..., g = Y + g2 Y^2 + ... (the linear
coefficients are normalised by the graded scalings X -> lam X), a -> A, b -> B extends to an
algebra isomorphism F_p[U] -> u iff [[A,B],A] = [[A,B],B] = 1 (then it is onto, dims p^3 agree).
Prints the set E of pairs (f, g) that extend, as coefficient tuples.
Usage: python3 heis_formal.py p [maxdeg]   (maxdeg = highest coefficient varied, default p-1)
"""
import sys, itertools
import numpy as np

p = int(sys.argv[1]); md = int(sys.argv[2]) if len(sys.argv) > 2 else p - 1
idx = {}; mons = []
for i in range(p):
    for j in range(p):
        for k in range(p):
            idx[(i, j, k)] = len(mons); mons.append((i, j, k))
D = len(mons)
from math import comb, factorial
# structure constants: (X^i Y^j Z^k)(X^i' Y^j' Z^k') = sum_r C(i',r)C(j,r) r! (-1)^r X^{i+i'-r} Y^{j+j'-r} Z^{k+k'+r}
T = np.zeros((D, D, D), dtype=np.int64)
for (i, j, k) in mons:
    for (i2, j2, k2) in mons:
        for r in range(min(i2, j) + 1):
            I, J, K = i + i2 - r, j + j2 - r, k + k2 + r
            if I < p and J < p and K < p:
                T[idx[(i, j, k)], idx[(i2, j2, k2)], idx[(I, J, K)]] += comb(i2, r) * comb(j, r) * factorial(r) * (-1) ** r
T %= p


def mul(u, v):
    return np.einsum('a,b,abc->c', u, v, T) % p


def one():
    e = np.zeros(D, dtype=np.int64); e[idx[(0, 0, 0)]] = 1; return e


def poly(coefs, var):  # 1 + sum c_k var^k
    e = one()
    for k, c in enumerate(coefs, start=1):
        e[idx[(k, 0, 0) if var == 'X' else (0, k, 0)]] = (e[idx[(k, 0, 0) if var == 'X' else (0, k, 0)]] + c) % p
    return e


def inv_poly(coefs, var):  # inverse of 1+f in F_p[var]/var^p, via power series
    f = [0] + list(coefs) + [0] * p; f = f[:p]
    g = [1] + [0] * (p - 1)
    for n in range(1, p):
        g[n] = (-sum(f[k] * g[n - k] for k in range(1, n + 1))) % p
    return poly(g[1:], var)


def comm(u, ui, v, vi):
    return mul(mul(ui, vi), mul(u, v))


E = []
rng = [range(p)] * (md - 1)
for fa in itertools.product(*rng):
    fc = (1,) + fa + (0,) * (p - 1 - md)
    A, Ai = poly(fc, 'X'), inv_poly(fc, 'X')
    for gb in itertools.product(*rng):
        gc = (1,) + gb + (0,) * (p - 1 - md)
        B, Bi = poly(gc, 'Y'), inv_poly(gc, 'Y')
        C = comm(A, Ai, B, Bi); Ci = comm(B, Bi, A, Ai)
        if np.array_equal(comm(C, Ci, A, Ai), one()) and np.array_equal(comm(C, Ci, B, Bi), one()):
            E.append((fc, gc))
print("p", p, "pairs tested", p ** (2 * (md - 1)), "extendable", len(E))
for e in E[:60]:
    print("f =", e[0], " g =", e[1])
