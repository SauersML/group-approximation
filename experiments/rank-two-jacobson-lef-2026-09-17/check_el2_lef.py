#!/usr/bin/env python3
"""Check the mirror-gluing local embedding of EL_2(J), J = F_2<S,T | TS=1>.

Claim under test (research/binary-jacobson-el2-is-lef.md):
  theta(g) = beta_*( w0 * tau(g)^(-t) * w0 ),  tau: S<->T anti-automorphism,
  beta: J -> J^rev, S -> T', T -> S'   (J^rev = F_2<S',T' | S'T'=1>)
is a homomorphism EL_2(J) -> EL_2(J^rev) with the same Laurent symbol, and
  Phi_M(g) = [columns k <= M/2 from the Toeplitz action of g near 0,
              columns k >  M/2 from the action of theta(g) near M]
is multiplicative on balls, so EL_2(J) is LEF.

Test: for random words u in generators e12(a), e21(a) we compute
  (A) Phi_M(u) as the product of the glued generator matrices, and
  (B) glue(near(g_u), far(theta(g_u))) from the exact matrix g_u in M_2(J),
      with theta(g_u) computed from the exact inverse g_u^(-1).
A == B on every word shows Phi_M factors through the group EL_2(J).
Injectivity: distinct g_u give distinct Phi_M(u).
Control: gluing with the far end lifted WITHOUT the tau-twist (symbol x->x^-1)
or with a hard truncation fails the same test.
"""
import itertools
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
Q = frozenset({(0, 0), (1, 1)})  # 1 - ST = 1 + ST in char 2


def tau(x):
    """anti-automorphism S <-> T: S^i T^j -> S^j T^i"""
    return frozenset((j, i) for (i, j) in x)


# ---------- 2x2 matrices over J ----------

def mmul(A, B):
    return [[jadd(jmul(A[r][0], B[0][c]), jmul(A[r][1], B[1][c])) for c in range(2)]
            for r in range(2)]


def e12(a):
    return [[ONE, a], [ZERO, ONE]]


def e21(a):
    return [[ONE, ZERO], [a, ONE]]


W0 = [[ZERO, ONE], [ONE, ZERO]]
I2 = [[ONE, ZERO], [ZERO, ONE]]


def mkey(A):
    return tuple(tuple(sorted(A[r][c])) for r in range(2) for c in range(2))


def theta_formula(g_inv):
    """theta(g) as a matrix over J^rev, written in J-normal-form symbols (p,q)
    meaning beta(S^p T^q) = T'^p S'^q.  theta(g) = beta_*(w0 tau(g^-1)^t w0)."""
    tt = [[tau(g_inv[c][r]) for c in range(2)] for r in range(2)]  # transpose of tau(g^-1)
    return mmul(mmul(W0, tt), W0)


# ---------- actions on F_2^{[0,M]} x {1,2} ----------

def near_mono(mono, k, M):
    """S^i T^j on zeta_k in the Toeplitz action near 0 (truncated at M)."""
    i, j = mono
    if k < j:
        return None
    t = k - j + i
    return t if t <= M else None


def far_mono(mono, k, M):
    """beta(S^p T^q) = T'^p S'^q near M: S' = X kills zeta_M, T' = X^-1."""
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


def mat2mul(a, b):
    return (a.astype(np.int64) @ b.astype(np.int64) % 2).astype(np.uint8)


# ---------- test ----------

def coeffs(maxdeg):
    monos = [(i, j) for i in range(maxdeg + 1) for j in range(maxdeg + 1)]
    out = [frozenset({m}) for m in monos] + [Q, jadd(S, ONE), jadd(T, Q)]
    return out


def run(M=90, words=400, maxlen=7, maxdeg=2, seed=1, variant="twist"):
    rng = random.Random(seed)
    cs = coeffs(maxdeg)
    gens = []  # (J-matrix, J-matrix inverse, glued matrix)
    for a in cs:
        for kind in (e12, e21):
            g = kind(a)
            near = realize(g, M, near_mono)
            if variant == "twist":
                th = kind(tau(a))  # theta(e_ij(a)) = e_ij(beta tau a)
                far = realize(th, M, far_mono)
            elif variant == "notwist":
                far = realize(g, M, far_mono)  # beta_* only: symbol inverted
            else:  # hard truncation
                far = realize(g, M, near_mono)
            gens.append((g, g, glue(near, far, M)))  # e_ij(a)^-1 = e_ij(a) in char 2
    seen = {}
    fails = 0
    for _ in range(words):
        L = rng.randint(1, maxlen)
        word = [rng.randrange(len(gens)) for _ in range(L)]
        g = I2
        ginv = I2
        phi = np.eye(2 * (M + 1), dtype=np.uint8)
        for w in word:
            G, Ginv, P = gens[w]
            g = mmul(g, G)
            ginv = mmul(Ginv, ginv)
            phi = mat2mul(phi, P)
        assert mkey(mmul(g, ginv)) == mkey(I2)
        # the variant's own direct formula from the group element g alone
        if variant == "twist":
            far_g = realize(theta_formula(ginv), M, far_mono)
        elif variant == "notwist":
            far_g = realize(g, M, far_mono)
        else:
            far_g = realize(g, M, near_mono)
        B = glue(realize(g, M, near_mono), far_g, M)
        if not np.array_equal(phi, B):
            fails += 1
        key = mkey(g)
        pk = phi.tobytes()
        if key in seen and seen[key] != pk:
            fails += 1
        seen[key] = pk
    # injectivity on the sample
    distinct_g = len(seen)
    distinct_phi = len(set(seen.values()))
    return fails, distinct_g, distinct_phi


def head_and_involution(M=90):
    # head e12(Q): glued image is not the identity
    near = realize(e12(Q), M, near_mono)
    far = realize(e12(tau(Q)), M, far_mono)
    head = glue(near, far, M)
    ident = np.eye(2 * (M + 1), dtype=np.uint8)
    # Whitehead involution w = e12(S) e21(T) e12(S) = [[Q,S],[T,0]], w^2 = 1
    def G(kind, a):
        return glue(realize(kind(a), M, near_mono), realize(kind(tau(a)), M, far_mono), M)
    w = mat2mul(mat2mul(G(e12, S), G(e21, T)), G(e12, S))
    wJ = mmul(mmul(e12(S), e21(T)), e12(S))
    return (not np.array_equal(head, ident),
            np.array_equal(mat2mul(w, w), ident),
            mkey(wJ) == mkey([[Q, S], [T, ZERO]]))


def control_relation(variant, M=90):
    """Returns (relation holds in M_2(J), relation holds for the glued matrices)."""
    def G(kind, a):
        near = realize(kind(a), M, near_mono)
        if variant == "twist":
            far = realize(kind(tau(a)), M, far_mono)
        elif variant == "notwist":
            far = realize(kind(a), M, far_mono)
        else:
            far = realize(kind(a), M, near_mono)
        return glue(near, far, M)
    # braid relation of EL_2(J): e12(S) e21(T) e12(S) = [[Q,S],[T,0]] = e21(T) e12(S) e21(T)
    lhsJ = mmul(mmul(e12(S), e21(T)), e12(S))
    rhsJ = mmul(mmul(e21(T), e12(S)), e21(T))
    val_ok = mkey(lhsJ) == mkey(rhsJ)
    lhs = mat2mul(mat2mul(G(e12, S), G(e21, T)), G(e12, S))
    rhs = mat2mul(mat2mul(G(e21, T), G(e12, S)), G(e21, T))
    return val_ok, bool(np.array_equal(lhs, rhs))


if __name__ == "__main__":
    print("head nontrivial, Phi(w)^2 = 1, w = [[Q,S],[T,0]]:", head_and_involution())
    for v in ("twist", "notwist", "truncate"):
        print(f"braid relation e12(S)e21(T)e12(S) = e21(T)e12(S)e21(T); variant {v}: "
              f"(holds in EL_2(J), holds after gluing) = {control_relation(v)}")
    for variant in ("twist", "notwist", "truncate"):
        fails, dg, dp = run(variant=variant)
        print(f"variant={variant:9s} well-definedness failures={fails:4d} "
              f"distinct g={dg} distinct Phi={dp}")
    fails, dg, dp = run(variant="twist")
    sys.exit(0 if fails == 0 and dg == dp else 1)
