#!/usr/bin/env python3
"""Exact stabilizer lattices of torsion points for Eckhardt's Berend actions.

Setting (research/artifacts/berend-k-theory-quotient-obstruction-2026-09-05.md):
  a root of t^3+t^2-2t-1, units a and b_- = a+1, b_+ = -(a+1), acting on
  Z^3 = Z[a] (basis 1,a,a^2) by the integer matrices M_a, M_b.  The group is
  Gamma = <M_a, M_b> = Z^2 (exponent coordinates (n,m) <-> M_a^n M_b^m).

A torsion point of T^3 of order dividing N is a character
  chi_v(x) = exp(2 pi i <v,x>/N),  v in (Z/N)^3,
and gamma fixes chi_v iff M_gamma^T v = v mod N (transpose or inverse
transpose give the same stabilizer).  The stabilizer is a lattice
Stab(v) <= Z^2 containing e_A Z x e_B Z, e_* the orders of the transposes
mod N, so it is determined by an exact finite enumeration of residues.

Output: for each prime p in PRIMES and each sign, the first torsion point
(ordered by N, then lexicographically) with Stab(v) contained in p Z^2,
together with an exact Smith normal form of Z^2/Stab(v), the orbit size
(checked equal to the index) and the indices [Z^2 : H + Stab(v)] for a few
rank-one direct summands H.  Pure integer arithmetic; single-threaded.
"""
import itertools
import json
import sys
from math import gcd

MA = ((0, 0, 1), (1, 0, 2), (0, 1, -1))
MB_MINUS = ((1, 0, 1), (1, 1, 2), (0, 1, 0))
MB_PLUS = tuple(tuple(-x for x in row) for row in MB_MINUS)
I3 = ((1, 0, 0), (0, 1, 0), (0, 0, 1))


def mat_mul(X, Y, mod=None):
    Z = tuple(
        tuple(sum(X[i][k] * Y[k][j] for k in range(3)) for j in range(3))
        for i in range(3)
    )
    if mod is not None:
        Z = tuple(tuple(x % mod for x in row) for row in Z)
    return Z


def mat_add(X, Y):
    return tuple(tuple(X[i][j] + Y[i][j] for j in range(3)) for i in range(3))


def scal(c, X):
    return tuple(tuple(c * x for x in row) for row in X)


def transpose(X):
    return tuple(tuple(X[j][i] for j in range(3)) for i in range(3))


def det(X):
    return (
        X[0][0] * (X[1][1] * X[2][2] - X[1][2] * X[2][1])
        - X[0][1] * (X[1][0] * X[2][2] - X[1][2] * X[2][0])
        + X[0][2] * (X[1][0] * X[2][1] - X[1][1] * X[2][0])
    )


def sanity():
    A2 = mat_mul(MA, MA)
    # a (a^2 + a - 2) = 1  and  (a+1)(2 - a^2) = 1
    inv_a = mat_add(mat_add(A2, MA), scal(-2, I3))
    inv_b = mat_add(scal(2, I3), scal(-1, A2))
    assert mat_mul(MA, inv_a) == I3
    assert mat_mul(MB_MINUS, inv_b) == I3
    assert MB_MINUS == mat_add(I3, MA)
    assert mat_mul(MA, MB_MINUS) == mat_mul(MB_MINUS, MA)
    # characteristic polynomial of M_a is t^3 + t^2 - 2t - 1:
    A3 = mat_mul(A2, MA)
    lhs = mat_add(mat_add(mat_add(A3, A2), scal(-2, MA)), scal(-1, I3))
    assert lhs == ((0, 0, 0),) * 3
    return {"det_Ma": det(MA), "det_Mb_minus": det(MB_MINUS), "det_Mb_plus": det(MB_PLUS)}


def apply(X, v, N):
    return tuple(sum(X[i][k] * v[k] for k in range(3)) % N for i in range(3))


def order_mod(X, N):
    Y = tuple(tuple(x % N for x in row) for row in X)
    ident = tuple(tuple((1 % N) if i == j else 0 for j in range(3)) for i in range(3))
    P, k = Y, 1
    while P != ident:
        P = mat_mul(P, Y, N)
        k += 1
        if k > 10 ** 6:
            raise RuntimeError("order too large")
    return k


def hnf2(gens):
    """Hermite basis (upper triangular) of the lattice in Z^2 spanned by gens."""
    # lattice L; first column gcd of x-coordinates via row reduction
    rows = [list(g) for g in gens if g != (0, 0)]
    # compute d2 = gcd of y where x = 0 part after elimination, standard 2D HNF
    a, b = 0, 0  # current first basis vector (a, b)
    c = 0        # second basis vector (0, c)
    for x, y in rows:
        # combine (a,b) and (x,y)
        if x == 0:
            c = gcd(c, y)
            continue
        if a == 0:
            a, b = x, y
            continue
        # extended gcd on a, x
        g, s, t = egcd(a, x)
        na, nb = g, s * b + t * y
        # kernel vector: (x/g)*(a,b) - (a/g)*(x,y) = (0, (x*b - a*y)/g)
        c = gcd(c, (x * b - a * y) // g)
        a, b = na, nb
    if a < 0:
        a, b = -a, -b
    c = abs(c)
    if c:
        b %= c
    return (a, b), (0, c)


def egcd(a, b):
    if b == 0:
        return (abs(a), (1 if a >= 0 else -1), 0)
    g, s, t = egcd(b, a % b)
    return g, t, s - (a // b) * t


def smith2(basis):
    (a, b), (_, c) = basis
    det_ = abs(a * c)
    d1 = gcd(gcd(a, b), c)
    return d1, det_ // d1 if d1 else 0


def stabilizer(v, N, At, Bt, eA, eB):
    powA = {}
    w = v
    for k in range(eA):
        powA.setdefault(w, []).append(k)
        w = apply(At, w, N)
    gens = [(eA, 0), (0, eB)]
    w = v
    for m in range(eB):
        for k in powA.get(w, []):
            n = (eA - k) % eA
            gens.append((n, m))
        w = apply(Bt, w, N)
    return gens


def orbit_size(v, N, At, Bt):
    seen = {v}
    stack = [v]
    while stack:
        x = stack.pop()
        for X in (At, Bt):
            y = apply(X, x, N)
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return len(seen)


def index_with_summand(h, basis):
    # [Z^2 : <h> + Stab] = gcd of 2x2 minors of the matrix with rows h, basis
    rows = [h, basis[0], basis[1]]
    g = 0
    for r, s in itertools.combinations(rows, 2):
        g = gcd(g, r[0] * s[1] - r[1] * s[0])
    return g


def main():
    info = {"sanity": sanity(), "witnesses": []}
    PRIMES = (2, 3)
    NS = list(range(2, 17)) + [25, 27, 32]
    summands = [(1, 0), (0, 1), (1, 1), (1, -1), (2, 1), (1, 2), (3, -2)]
    for sign, MB in (("b_minus=a+1", MB_MINUS), ("b_plus=-(a+1)", MB_PLUS)):
        At, Bt = transpose(MA), transpose(MB)
        found = {p: None for p in PRIMES}
        for N in NS:
            if all(found.values()):
                break
            eA, eB = order_mod(At, N), order_mod(Bt, N)
            for v in itertools.product(range(N), repeat=3):
                if gcd(gcd(gcd(v[0], v[1]), v[2]), N) != 1:
                    continue  # exact order N only
                pending = [p for p in PRIMES if found[p] is None]
                if not pending:
                    break
                gens = stabilizer(v, N, At, Bt, eA, eB)
                basis = hnf2(gens)
                d1, d2 = smith2(basis)
                for p in pending:
                    if all(x % p == 0 and y % p == 0 for x, y in gens):
                        osz = orbit_size(v, N, At, Bt)
                        assert osz == d1 * d2, (osz, d1, d2)
                        # re-verify basis vectors really stabilize v
                        for bvec in basis:
                            n, m = bvec
                            w = v
                            for _ in range(n % eA):
                                w = apply(At, w, N)
                            for _ in range(m % eB):
                                w = apply(Bt, w, N)
                            assert w == v
                        found[p] = {
                            "sign": sign,
                            "p": p,
                            "N": N,
                            "v": v,
                            "orders_mod_N": [eA, eB],
                            "stab_hnf_basis": [list(basis[0]), list(basis[1])],
                            "smith_invariants": [d1, d2],
                            "orbit_size": osz,
                            "index_H_plus_stab": {str(h): index_with_summand(h, basis) for h in summands},
                        }
        info["witnesses"].extend(found[p] for p in PRIMES)
    json.dump(info, sys.stdout, indent=1)
    print()


if __name__ == "__main__":
    main()
