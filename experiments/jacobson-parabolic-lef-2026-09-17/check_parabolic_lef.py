#!/usr/bin/env python3
"""Check the local embedding of the column parabolic P = J^2 x| EL_2(J) <= EL_3(J).

J = F_2<S,T | TS=1>, Q = 1 - ST.  An element of P is a pair (g, v) standing for
the 3x3 matrix [[g, v], [0, 1]] with g in EL_2(J), v in J^2 (a column):

    (g, v) (g', v') = (g g', v + g v').

Claim under test (research/jacobson-rank-three-parabolics-are-lef.md):

    Psi_{M,d}(g, v) = ( Phi_M(g),  ev_d(v) )   in   W^d x| GL(W),
    W = F_2^{[0,M]} (x) F_2^2,
    Phi_M(g) = mirror-glued model of binary-jacobson-el2-is-lef,
    ev_d(v) = ( v e_0, ..., v e_{d-1} ) truncated to [0,M],

multiplies like the group on balls, and is injective on balls.  The
affine group W^d x| GL(W) has product (A, U)(A', U') = (A A', U + A U').

Test A (well defined / multiplicative): for random words in the generators
  e12(a), e21(a), c1(a) = x_13(a), c2(a) = x_23(a),
the product of the generator images equals Psi of the exact group element.
Test B (injective): distinct exact elements have distinct images.
Test C (relations and head): the three-index Steinberg commutators
  [e12(a), c2(b)] = c1(ab),   [e21(a), c1(b)] = c2(ab)
hold for the images, and the head c1(Q) has nontrivial image.
Control: replace Phi_M by the hard truncation (no mirror end); Test A fails.
"""
import random
import sys

import numpy as np

# ---------- the ring J: F_2-span of S^i T^j (normal form, TS = 1) ----------


def jmul_mono(a, b):
    i, j = a
    k, l = b
    if j <= k:
        return (i + k - j, l)
    return (i, j - k + l)


def jadd(x, y):
    return frozenset(set(x) ^ set(y))


def jmul(x, y):
    out = set()
    for a in x:
        for b in y:
            out ^= {jmul_mono(a, b)}
    return frozenset(out)


ZERO = frozenset()
ONE = frozenset({(0, 0)})
S = frozenset({(1, 0)})
T = frozenset({(0, 1)})
Q = frozenset({(0, 0), (1, 1)})


def tau(x):
    return frozenset((j, i) for (i, j) in x)


# ---------- 2x2 matrices and 2-columns over J ----------


def mmul(A, B):
    return [[jadd(jmul(A[r][0], B[0][c]), jmul(A[r][1], B[1][c])) for c in range(2)]
            for r in range(2)]


def mvec(A, v):
    return (jadd(jmul(A[0][0], v[0]), jmul(A[0][1], v[1])),
            jadd(jmul(A[1][0], v[0]), jmul(A[1][1], v[1])))


def vadd(v, w):
    return (jadd(v[0], w[0]), jadd(v[1], w[1]))


I2 = [[ONE, ZERO], [ZERO, ONE]]
W0 = [[ZERO, ONE], [ONE, ZERO]]
V0 = (ZERO, ZERO)


def pmul(x, y):
    g, v = x
    h, w = y
    return (mmul(g, h), vadd(v, mvec(g, w)))


def pinv(x, ginv):
    """inverse of (g, v) is (g^-1, -g^-1 v); char 2."""
    g, v = x
    return (ginv, mvec(ginv, v))


def pkey(x):
    g, v = x
    return (tuple(tuple(sorted(g[r][c])) for r in range(2) for c in range(2)),
            tuple(tuple(sorted(v[r])) for r in range(2)))


def theta_formula(g_inv):
    tt = [[tau(g_inv[c][r]) for c in range(2)] for r in range(2)]
    return mmul(mmul(W0, tt), W0)


# ---------- actions on W = F_2^{[0,M]} x {1,2} ----------


def near_mono(mono, k, M):
    i, j = mono
    if k < j:
        return None
    t = k - j + i
    return t if t <= M else None


def far_mono(mono, k, M):
    p, q = mono
    t = k + q
    if t > M:
        return None
    t = t - p
    return t if t >= 0 else None


def realize(A, M, action):
    n = 2 * (M + 1)
    mat = np.zeros((n, n), dtype=np.uint8)
    for k in range(M + 1):
        for c in range(2):
            col = 2 * k + c
            for r in range(2):
                for mono in A[r][c]:
                    t = action(mono, k, M)
                    if t is not None:
                        mat[2 * t + r, col] ^= 1
    return mat


def glue(near_mat, far_mat, M):
    out = far_mat.copy()
    half = 2 * (M // 2 + 1)
    out[:, :half] = near_mat[:, :half]
    return out


def phi_exact(g, ginv, M, variant):
    near = realize(g, M, near_mono)
    if variant == "twist":
        far = realize(theta_formula(ginv), M, far_mono)
    else:
        far = near
    return glue(near, far, M)


def ev(v, M, d):
    """ev_d(v)[:, s] = v e_s in W, i.e. column s holds (v_1 e_s, v_2 e_s)."""
    U = np.zeros((2 * (M + 1), d), dtype=np.uint8)
    for s in range(d):
        for r in range(2):
            for mono in v[r]:
                t = near_mono(mono, s, M)
                if t is not None:
                    U[2 * t + r, s] ^= 1
    return U


def mat2mul(a, b):
    return (a.astype(np.int64) @ b.astype(np.int64) % 2).astype(np.uint8)


def amul(X, Y):
    A, U = X
    B, V = Y
    return (mat2mul(A, B), U ^ mat2mul(A, V))


def aeq(X, Y):
    return np.array_equal(X[0], Y[0]) and np.array_equal(X[1], Y[1])


# ---------- generators ----------


def coeffs(maxdeg):
    monos = [(i, j) for i in range(maxdeg + 1) for j in range(maxdeg + 1)]
    return [frozenset({m}) for m in monos] + [Q, jadd(S, ONE), jadd(T, Q)]


def generators(M, d, variant, maxdeg=2):
    gens = []
    for a in coeffs(maxdeg):
        for kind in ("e12", "e21", "c1", "c2"):
            if kind == "e12":
                x = ([[ONE, a], [ZERO, ONE]], V0)
            elif kind == "e21":
                x = ([[ONE, ZERO], [a, ONE]], V0)
            elif kind == "c1":
                x = (I2, (a, ZERO))
            else:
                x = (I2, (ZERO, a))
            g = x[0]
            # every generator is an involution in char 2, so g^-1 = g
            img = (phi_exact(g, g, M, variant), ev(x[1], M, d))
            gens.append((x, x[0], img))
    return gens


def psi_exact(x, ginv, M, d, variant):
    return (phi_exact(x[0], ginv, M, variant), ev(x[1], M, d))


def run(M=100, d=8, words=400, maxlen=7, seed=7, variant="twist"):
    rng = random.Random(seed)
    gens = generators(M, d, variant)
    ident = (np.eye(2 * (M + 1), dtype=np.uint8), np.zeros((2 * (M + 1), d), dtype=np.uint8))
    seen = {}
    fails = 0
    for _ in range(words):
        L = rng.randint(1, maxlen)
        word = [rng.randrange(len(gens)) for _ in range(L)]
        x = (I2, V0)
        ginv = I2
        img = ident
        for w in word:
            gx, gxinv, gimg = gens[w]
            x = pmul(x, gx)
            ginv = mmul(gxinv, ginv)
            img = amul(img, gimg)
        assert pkey((mmul(x[0], ginv), V0)) == pkey((I2, V0))
        direct = psi_exact(x, ginv, M, d, variant)
        if not aeq(img, direct):
            fails += 1
        key = pkey(x)
        ib = img[0].tobytes() + img[1].tobytes()
        if key in seen and seen[key] != ib:
            fails += 1
        seen[key] = ib
    return fails, len(seen), len(set(seen.values()))


def relations(M=100, d=8):
    gens = {}
    ok = True

    def img(kind, a):
        if kind == "e12":
            x = ([[ONE, a], [ZERO, ONE]], V0)
        elif kind == "e21":
            x = ([[ONE, ZERO], [a, ONE]], V0)
        elif kind == "c1":
            x = (I2, (a, ZERO))
        else:
            x = (I2, (ZERO, a))
        return x, psi_exact(x, x[0], M, d, "twist")

    def comm(X, Y):  # [X,Y] = X Y X^-1 Y^-1 = X Y X Y for involutions
        return amul(amul(amul(X, Y), X), Y)

    cs = coeffs(2)
    for a in cs:
        for b in cs:
            _, A = img("e12", a)
            _, B = img("c2", b)
            _, C = img("c1", jmul(a, b))
            ok &= aeq(comm(A, B), C)
            _, A = img("e21", a)
            _, B = img("c1", b)
            _, C = img("c2", jmul(a, b))
            ok &= aeq(comm(A, B), C)
    _, H = img("c1", Q)
    head_nontrivial = bool(H[1].any())
    return ok, head_nontrivial


def a2_closed_subsets_lie_in_parabolics():
    """Brute force over all 2^6 subsets of the A_2 roots e_i - e_j.

    Returns (number of closed subsets, number of proper closed subsets,
    number of proper closed subsets contained in no maximal parabolic set
    {alpha : lambda(alpha) >= 0}), lambda ranging over the six weights
    obtained by permuting (1,1,0) and (1,0,0).  The last number must be 0.
    """
    from itertools import permutations
    roots = [(i, j) for i in range(3) for j in range(3) if i != j]

    def add(a, b):  # (e_i - e_j) + (e_j - e_k) = e_i - e_k
        if a[1] == b[0] and a[0] != b[1]:
            return (a[0], b[1])
        if b[1] == a[0] and b[0] != a[1]:
            return (b[0], a[1])
        return None

    lams = set(permutations((1, 1, 0))) | set(permutations((1, 0, 0)))
    pars = [frozenset(r for r in roots if lam[r[0]] - lam[r[1]] >= 0) for lam in lams]
    closed = proper = bad = 0
    for mask in range(1 << 6):
        sub = frozenset(roots[k] for k in range(6) if mask >> k & 1)
        if any(add(a, b) is not None and add(a, b) not in sub for a in sub for b in sub):
            continue
        closed += 1
        if len(sub) == 6:
            continue
        proper += 1
        if not any(sub <= p for p in pars):
            bad += 1
    return closed, proper, bad


if __name__ == "__main__":
    nclosed, nproper, nbad = a2_closed_subsets_lie_in_parabolics()
    print(f"A_2: closed subsets={nclosed} proper={nproper} "
          f"proper and in no maximal parabolic set={nbad}")
    rel_ok, head = relations()
    print("three-index Steinberg commutators hold in the model:", rel_ok)
    print("head x_13(Q) has nontrivial image:", head)
    res = {}
    for variant in ("twist", "truncate"):
        fails, dg, dp = run(variant=variant)
        res[variant] = (fails, dg, dp)
        print(f"variant={variant:9s} multiplicativity failures={fails:4d} "
              f"distinct elements={dg} distinct images={dp}")
    f, dg, dp = res["twist"]
    good = (rel_ok and head and f == 0 and dg == dp and res["truncate"][0] > 0
            and nbad == 0)
    sys.exit(0 if good else 1)
