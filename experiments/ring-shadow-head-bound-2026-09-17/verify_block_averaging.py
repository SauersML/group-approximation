#!/usr/bin/env python3
"""Exhaustive check of the pointwise block-averaging lemma behind
leavitt-cone-head-bound-holds-for-all-ring-shadows.

Setting.  B is a finite F_2-algebra (given by a multiplication table on an
F_2-basis; elements and functionals are bitmasks).  X = M_{p x r}(B) is the
additive group of the block root group {x_ik(a): i in I, k in K}.  A character
of X is c = (c_ik), c_ik in Hom_{F_2}(B, F_2).  For e in B put

  h_e(c) = average over g = 1 + sum_{j>=2} b'_j E_j1 (left), h = 1 + sum_{l>=2} b_l E_1l
           (right), and row/column permutations (sigma, tau), of
           1[ psi_c( sigma tau . (g (e E_11) h) ) = -1 ],

computed by literally multiplying block matrices over B (no closed formula used).
Invariance of the spectral measure mu under these maps gives m(e) = E_mu h_e(c).

Checked, for every character c and every e in B:
  (U)  h_e(c) <= 1[A(c,e) nonempty]
  (L)  h_e(c) >= kappa * 1[A(c,e) nonempty],  kappa = (1/4)(1-1/p)(1-1/r),
where A(c,e) = {(j,l): c_jl does not vanish on the two-sided ideal BeB};
and that J(c) = {e : A(c,e) empty} is a two-sided ideal.
Exit code 0 iff every check passes.
"""
import itertools
import sys


def make_ring(name, n, mul_basis):
    """mul_basis[i][j] = bitmask of product of basis elements i, j."""
    N = 1 << n

    def mul(x, y):
        out = 0
        for i in range(n):
            if not (x >> i) & 1:
                continue
            for j in range(n):
                if (y >> j) & 1:
                    out ^= mul_basis[i][j]
        return out

    table = [[mul(x, y) for y in range(N)] for x in range(N)]
    one = [x for x in range(N) if all(table[x][y] == y and table[y][x] == y for y in range(N))]
    assert len(one) == 1, name
    return {"name": name, "n": n, "N": N, "mul": table, "one": one[0]}


def rings():
    rs = []
    # F_2[eps]/eps^2 : basis 1, eps
    rs.append(make_ring("F2[e]/e^2", 2, [[1, 2], [2, 0]]))
    # F_2 x F_2 : basis e1, e2 (idempotents)
    rs.append(make_ring("F2xF2", 2, [[1, 0], [0, 2]]))
    # F_4 : basis 1, w with w^2 = w + 1
    rs.append(make_ring("F4", 2, [[1, 2], [2, 3]]))
    # F_2[x]/x^3 : basis 1, x, x^2
    rs.append(make_ring("F2[x]/x^3", 3, [[1, 2, 4], [2, 4, 0], [4, 0, 0]]))
    # upper triangular T_2(F_2): basis E11, E12, E22
    rs.append(make_ring("T2(F2)", 3, [[1, 2, 0], [0, 0, 2], [0, 0, 4]]))
    # F_2[x,y]/(x,y)^2 : basis 1, x, y
    rs.append(make_ring("F2[x,y]/m^2", 3, [[1, 2, 4], [2, 0, 0], [4, 0, 0]]))
    return rs


def parity(v):
    return bin(v).count("1") & 1


def matmul(R, A, Bm):
    mul = R["mul"]
    rows, inner, cols = len(A), len(Bm), len(Bm[0])
    out = [[0] * cols for _ in range(rows)]
    for i in range(rows):
        for k in range(cols):
            s = 0
            for j in range(inner):
                s ^= mul[A[i][j]][Bm[j][k]]
            out[i][k] = s
    return out


def check_ring(R, p, r):
    N, one, mul = R["N"], R["one"], R["mul"]
    kappa = 0.25 * (1 - 1 / p) * (1 - 1 / r)
    perms_p = list(itertools.permutations(range(p)))
    perms_r = list(itertools.permutations(range(r)))
    # precompute the conjugated block matrices M(e; b', b) = g (e E_11) h
    blocks = {}
    for e in range(N):
        mats = []
        for bp in itertools.product(range(N), repeat=p - 1):
            g = [[one if i == j else 0 for j in range(p)] for i in range(p)]
            for j in range(1, p):
                g[j][0] = bp[j - 1]
            for b in itertools.product(range(N), repeat=r - 1):
                h = [[one if i == j else 0 for j in range(r)] for i in range(r)]
                for l in range(1, r):
                    h[0][l] = b[l - 1]
                E = [[0] * r for _ in range(p)]
                E[0][0] = e
                mats.append(matmul(R, matmul(R, g, E), h))
        blocks[e] = mats
    # two-sided ideal spans BeB
    span = {}
    for e in range(N):
        gens = {mul[mul[x][e]][y] for x in range(N) for y in range(N)}
        sp = {0}
        for gnr in gens:
            sp |= {s ^ gnr for s in sp}
        span[e] = sp
    worst = 1.0
    nchars = 0
    for c in itertools.product(range(N), repeat=p * r):
        nchars += 1
        C = [list(c[i * r:(i + 1) * r]) for i in range(p)]
        J = []
        for e in range(N):
            A = any(parity(C[j][l] & x) for j in range(p) for l in range(r) for x in span[e])
            if not A:
                J.append(e)
            tot = 0
            cnt = 0
            for s in perms_p:
                for t in perms_r:
                    # permuted character: (sigma,tau).c
                    Cp = [[C[s[i]][t[k]] for k in range(r)] for i in range(p)]
                    for M in blocks[e]:
                        v = 0
                        for i in range(p):
                            for k in range(r):
                                v ^= parity(Cp[i][k] & M[i][k])
                        tot += v
                        cnt += 1
            hval = tot / cnt
            if A:
                if hval < kappa - 1e-12:
                    print("FAIL (L)", R["name"], C, e, hval)
                    return False
                worst = min(worst, hval)
            elif hval != 0:
                print("FAIL (U)", R["name"], C, e, hval)
                return False
        Js = set(J)
        for x in J:
            for y in J:
                if x ^ y not in Js:
                    print("FAIL ideal +", R["name"], C)
                    return False
            for b in range(N):
                if mul[b][x] not in Js or mul[x][b] not in Js:
                    print("FAIL ideal mult", R["name"], C)
                    return False
    print(f"{R['name']:>12}  p=r={p}  chars={nchars}  min h on A-nonempty = {worst:.4f}  kappa = {kappa:.4f}  OK")
    return True


def main():
    ok = True
    for R in rings():
        ok &= check_ring(R, 2, 2)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
