#!/usr/bin/env python3
"""Exact checks for the Sol-lattice calibration of Zaremsky Problem 1.17.

G = Z^2 x|_M Z with M in GL_2(Z) hyperbolic acts on R^2 by affine maps
t.p = M p, a.p = p + e1, b.p = p + e2 (|det| = 1).

Check 1 (orbit polygon area). For w_n = [t^n a t^-n, t^-n a t^n] and ANY base
point p0, the shoelace area of the closed polygon (g_0 p0, g_1 p0, ..., g_m p0),
g_i the prefixes of w_n, equals det(M^n e1, M^-n e1) / 2 * 2 = det(u, v) with
u = M^n e1, v = M^-n e1 (shoelace convention: signed area = 1/2 sum q_i ^ q_{i+1}).

Check 2 (unique fixed points). det(M^k - I) != 0 for 1 <= |k| <= 30.

Check 3 (logarithmic fiber length). For v in Z^2 nonzero and integers m, the
two-sided greedy expansion m = sum_{j=0}^K c_j lam^j + sum_{j=1}^K d_j lam^-j + s
with bounded digits and s in a finite set yields a word for m*v of length O(log m).
We construct the vector identity exactly in Z^2 and report word length / log m.

Exact rational arithmetic only. Single-threaded, small.
"""
from fractions import Fraction as Fr
import math
import random
import sys


def mat_mul(A, B):
    return [[A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]],
            [A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]]]


def mat_inv(A):
    det = A[0][0] * A[1][1] - A[0][1] * A[1][0]
    assert det in (1, -1)
    return [[A[1][1] * det, -A[0][1] * det], [-A[1][0] * det, A[0][0] * det]]


def mat_pow(A, k):
    if k < 0:
        A = mat_inv(A)
        k = -k
    R = [[1, 0], [0, 1]]
    for _ in range(k):
        R = mat_mul(R, A)
    return R


def apply(A, p):
    return (A[0][0] * p[0] + A[0][1] * p[1], A[1][0] * p[0] + A[1][1] * p[1])


def det2(p, q):
    return p[0] * q[1] - p[1] * q[0]


def word_wn(n):
    # letters: 't', 'T' (t^-1), 'a', 'A' (a^-1)
    Aw = 't' * n + 'a' + 'T' * n          # t^n a t^-n
    Bw = 'T' * n + 'a' + 't' * n          # t^-n a t^n
    inv = {'t': 'T', 'T': 't', 'a': 'A', 'A': 'a'}
    Ainv = ''.join(inv[c] for c in reversed(Aw))
    Binv = ''.join(inv[c] for c in reversed(Bw))
    return Aw + Bw + Ainv + Binv


def orbit_polygon(word, M, p0):
    Minv = mat_inv(M)
    # affine map g = (L, c): p -> L p + c ; prefix product g_i = g_{i-1} s_i
    L = [[1, 0], [0, 1]]
    c = (Fr(0), Fr(0))
    pts = [p0]
    gen = {
        't': (M, (0, 0)),
        'T': (Minv, (0, 0)),
        'a': ([[1, 0], [0, 1]], (1, 0)),
        'A': ([[1, 0], [0, 1]], (-1, 0)),
    }
    for ch in word:
        Ls, cs = gen[ch]
        # (L,c) o (Ls,cs): p -> L(Ls p + cs) + c
        c_new = apply(L, cs)
        c = (c[0] + c_new[0], c[1] + c_new[1])
        L = mat_mul(L, Ls)
        q = apply(L, p0)
        pts.append((q[0] + c[0], q[1] + c[1]))
    return L, c, pts


def shoelace(pts):
    s = Fr(0)
    for i in range(len(pts) - 1):
        s += det2(pts[i], pts[i + 1])
    return s / 2


def check1(M, name, nmax=10, trials=3):
    rng = random.Random(12345)
    for n in range(1, nmax + 1):
        u = apply(mat_pow(M, n), (1, 0))
        v = apply(mat_pow(M, -n), (1, 0))
        target = det2(u, v)
        for _ in range(trials):
            p0 = (Fr(rng.randint(-50, 50), rng.randint(1, 9)), Fr(rng.randint(-50, 50), rng.randint(1, 9)))
            L, c, pts = orbit_polygon(word_wn(n), M, p0)
            assert L == [[1, 0], [0, 1]] and c == (0, 0), "w_n not trivial?"
            assert pts[0] == pts[-1]
            area = shoelace(pts)
            if area != target:
                print("MISMATCH", name, n, p0, area, target)
                sys.exit(1)
        print(f"check1 {name} n={n:2d} |w_n|={len(word_wn(n)):3d} area=det(u,v)={target}")


def check2(M, name):
    for k in list(range(1, 31)) + list(range(-30, 0)):
        Mk = mat_pow(M, k)
        d = (Mk[0][0] - 1) * (Mk[1][1] - 1) - Mk[0][1] * Mk[1][0]
        assert d != 0, (name, k)
    print(f"check2 {name}: det(M^k - I) != 0 for 1 <= |k| <= 30")


def check3(M, name, v=(1, 2)):
    # lam = larger |eigenvalue|, conj = other; tr, det
    tr = M[0][0] + M[1][1]
    de = M[0][0] * M[1][1] - M[0][1] * M[1][0]
    disc = tr * tr - 4 * de
    assert disc > 0 and int(math.isqrt(disc)) ** 2 != disc
    r1 = (tr + math.sqrt(disc)) / 2
    r2 = (tr - math.sqrt(disc)) / 2
    lam, lamb = (r1, r2) if abs(r1) > abs(r2) else (r2, r1)
    Minv = mat_inv(M)
    for m in [10 ** e for e in range(2, 13)]:
        # greedy on x = m with powers lam^j (j>=0): coefficients c_j
        K = max(1, math.ceil(math.log(m) / math.log(abs(lam))) + 1)
        x = float(m)
        cs = {}
        for j in range(K, -1, -1):
            cj = round(x / lam ** j)
            cs[j] = cj
            x -= cj * lam ** j
        # conjugate of remainder r = m - sum c_j lam^j is m - sum c_j lamb^j
        xb = float(m) - sum(cj * lamb ** j for j, cj in cs.items())
        ds = {}
        for j in range(K + 2, 0, -1):
            # conjugate of lam^-j is lamb^-j, |lamb^-j| = |lam|^j large
            dj = round(xb / lamb ** (-j))
            ds[j] = dj
            xb -= dj * lamb ** (-j)
        # exact integer vector identity: s(M) v := m v - sum c_j M^j v - sum d_j M^-j v
        acc = (m * v[0], m * v[1])
        for j, cj in cs.items():
            w = apply(mat_pow(M, j), v)
            acc = (acc[0] - cj * w[0], acc[1] - cj * w[1])
        for j, dj in ds.items():
            w = apply(mat_pow(M, -j), v)
            acc = (acc[0] - dj * w[0], acc[1] - dj * w[1])
        digits = sum(abs(c) for c in cs.values()) + sum(abs(d) for d in ds.values())
        # word length of t-Horner word: 2K t-letters each way + digit letters (|v|_1 per unit digit) + |s|_1
        vlen = abs(v[0]) + abs(v[1])
        wordlen = 4 * (K + 2) + digits * vlen + abs(acc[0]) + abs(acc[1])
        maxdig = max([abs(c) for c in cs.values()] + [abs(d) for d in ds.values()])
        print(f"check3 {name} m=1e{int(round(math.log10(m)))} K={K} max|digit|={maxdig} "
              f"residual s(M)v={acc} wordlen<={wordlen} wordlen/log(m)={wordlen / math.log(m):.2f}")


if __name__ == "__main__":
    mats = {"[[2,1],[1,1]]": [[2, 1], [1, 1]], "[[1,1],[1,0]] (det -1)": [[1, 1], [1, 0]], "[[3,2],[1,1]]": [[3, 2], [1, 1]]}
    for name, M in mats.items():
        check1(M, name, nmax=10, trials=3)
        check2(M, name)
        check3(M, name)
    print("ALL CHECKS PASSED")
