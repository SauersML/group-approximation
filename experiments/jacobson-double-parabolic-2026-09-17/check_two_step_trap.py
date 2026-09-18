#!/usr/bin/env python3
"""Checks for research/jacobson-double-parabolic-two-step-models-kill-head.md.

J = F_2<S,T | TS=1>, Q = 1 - ST = 1 + ST (char 2).  P_{2,2} <= EL_4(J) is the
group of block matrices [[A, Y], [0, B]], A, B in EL_2(J), Y in M_2(J).

Part 1 (exact group identities).  Every conjugation and product identity in
P_{2,2} used by the proof is checked with exact 4x4 matrix arithmetic over J.

Part 2 (sharpness control: the right Levi is needed).  The one-sided parabolic
J^2 x| EL_2(J) <= EL_3(J) has the two-step model
    [[Phi_M(g), ev_d(v)], [0, 1]]
of research/jacobson-rank-three-parabolics-lef-proof.md.  In that model, with
H = Hom(F^d, W_1), c_l(X) = Phi(l) X and
    Lambda(a) = (c_{x12(a)} - 1)(c_{x21(1)} - 1),   v = ev_d(e_1),
we check Lambda(T)Lambda(S) v = v but Lambda(S)Lambda(T) v != v: the head
survives, and the cyclic space of the left operators is NOT a space on which
Lambda(T)Lambda(S) = 1.  The proof's extra input, the commuting right-Levi
algebra, is exactly what is missing there.

Part 3 (the linear-algebra step).  Random search over small F_2 examples of
the hypotheses of the "commuting trap" lemma: commuting pairs of operator
families (Lam_S, Lam_T), (M_S, M_T) and v with Lam_S v = M_S v,
Lam_T v = M_T v, Lam_T Lam_S v = v; every hit must satisfy Lam_S Lam_T v = v.
"""
import importlib.util
import os
import random
import sys

import numpy as np

# ---------------- the ring J ----------------


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
ST = frozenset({(1, 1)})
Q = frozenset({(0, 0), (1, 1)})

# ---------------- 4x4 matrices over J ----------------


def mat_id():
    return tuple(tuple(ONE if r == c else ZERO for c in range(4)) for r in range(4))


def mat_mul(A, B):
    out = []
    for r in range(4):
        row = []
        for c in range(4):
            acc = ZERO
            for k in range(4):
                acc = jadd(acc, jmul(A[r][k], B[k][c]))
            row.append(acc)
        out.append(tuple(row))
    return tuple(out)


def x(i, j, a):
    """elementary matrix x_ij(a), indices 1..4"""
    M = [list(r) for r in mat_id()]
    M[i - 1][j - 1] = jadd(M[i - 1][j - 1], a)
    return tuple(tuple(r) for r in M)


def n(entries):
    """n(Y) = [[1, Y], [0, 1]] with Y given as {(i,j): a}, i in {1,2}, j in {3,4}"""
    M = [list(r) for r in mat_id()]
    for (i, j), a in entries.items():
        assert i in (1, 2) and j in (3, 4)
        M[i - 1][j - 1] = jadd(M[i - 1][j - 1], a)
    return tuple(tuple(r) for r in M)


def conj(l, g):
    """l g l^{-1}; every Levi generator used is an involution in char 2"""
    assert mat_mul(l, l) == mat_id()
    return mat_mul(mat_mul(l, g), l)


def part1():
    checks = []
    Y = lambda a: {(1, 3): a}           # Y_a = E_11 (x) a  <->  x_13(a)
    # (1) left x_21(1):  n(Y_a) -> n(Y_a + E_21 (x) a)
    for a in (ONE, S, T):
        checks.append(conj(x(2, 1, ONE), n(Y(a))) == n({(1, 3): a, (2, 3): a}))
    # (2) left x_12(b): n(E_21 (x) a) -> n(E_21 (x) a + E_11 (x) b a)
    for (b, a) in ((S, ONE), (T, ONE), (T, S), (S, T)):
        checks.append(conj(x(1, 2, b), n({(2, 3): a}))
                      == n({(2, 3): a, (1, 3): jmul(b, a)}))
    # (3) right x_34(1): n(Y_1) -> n(Y_1 + E_12 (x) 1) = n(Y B^{-1}), B = x_34(1)
    checks.append(conj(x(3, 4, ONE), n(Y(ONE))) == n({(1, 3): ONE, (1, 4): ONE}))
    # (4) right x_43(b): n(E_12 (x) 1) -> n(E_12 (x) 1 + E_11 (x) b)
    for b in (S, T):
        checks.append(conj(x(4, 3, b), n({(1, 4): ONE}))
                      == n({(1, 4): ONE, (1, 3): b}))
    # (5) TS = 1, so the (T,S) instance of (2) returns Y_1
    checks.append(jmul(T, S) == ONE)
    # (6) additivity in N and Q = 1 + ST
    checks.append(mat_mul(n(Y(ONE)), n(Y(ST))) == n(Y(Q)))
    checks.append(jadd(ONE, jmul(S, T)) == Q)
    # (7) left and right Levi generators commute
    for l in (x(1, 2, S), x(1, 2, T), x(2, 1, ONE)):
        for r in (x(3, 4, ONE), x(4, 3, S), x(4, 3, T)):
            checks.append(mat_mul(l, r) == mat_mul(r, l))
    # (8) the head is not the identity
    checks.append(n(Y(Q)) != mat_id())
    return all(checks), len(checks)


# ---------------- Part 2: the one-sided control ----------------


def load_parabolic_module():
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "..", "jacobson-parabolic-lef-2026-09-17",
                        "check_parabolic_lef.py")
    spec = importlib.util.spec_from_file_location("check_parabolic_lef", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def part2(M=60, d=6):
    P = load_parabolic_module()
    e12 = lambda a: [[P.ONE, a], [P.ZERO, P.ONE]]
    e21 = lambda a: [[P.ONE, P.ZERO], [a, P.ONE]]
    phi = lambda g: P.phi_exact(g, g, M, "twist")  # generators are involutions
    I = np.eye(2 * (M + 1), dtype=np.uint8)
    D21 = phi(e21(P.ONE)) ^ I
    Lam = {name: P.mat2mul(phi(e12(a)) ^ I, D21) for name, a in (("S", P.S), ("T", P.T))}
    ev = lambda a: P.ev((a, P.ZERO), M, d)
    v = ev(P.ONE)
    TSv = P.mat2mul(Lam["T"], P.mat2mul(Lam["S"], v))
    STv = P.mat2mul(Lam["S"], P.mat2mul(Lam["T"], v))
    ok_ts = np.array_equal(TSv, v)                      # Lambda(T)Lambda(S) v = v
    ok_st_formula = np.array_equal(STv, ev(P.jmul(P.S, P.T)))
    head = v ^ STv                                      # = ev(Q) != 0
    head_alive = bool(head.any()) and np.array_equal(head, ev(P.Q))
    return ok_ts, ok_st_formula, head_alive


# ---------------- Part 3: the commuting trap, brute force ----------------


def all_mats(k):
    out = []
    for m in range(1 << (k * k)):
        out.append(np.array([[(m >> (r * k + c)) & 1 for c in range(k)]
                             for r in range(k)], dtype=np.int64))
    return out


def part3(p=2, q=2):
    """H = F_2^p (x) F_2^q, Lam = L (x) 1, M = 1 (x) R: the two families commute.
    Exhaustive over L_S, L_T, R_S, R_T and all v."""
    mats_p = all_mats(p)
    mats_q = all_mats(q)
    dim = p * q
    V = np.array([[(m >> i) & 1 for m in range(1 << dim)] for i in range(dim)],
                 dtype=np.int64)
    Ip = np.eye(p, dtype=np.int64)
    Iq = np.eye(q, dtype=np.int64)
    kron_L = [np.kron(L, Iq) % 2 for L in mats_p]
    kron_R = [np.kron(Ip, R) % 2 for R in mats_q]
    hits = nontrivial = bad = 0
    for LS in kron_L:
        for LT in kron_L:
            TS = (LT @ LS) % 2
            ST_ = (LS @ LT) % 2
            ts_fix = np.all((TS @ V) % 2 == V, axis=0)
            if not ts_fix[1:].any():
                continue
            LSV = (LS @ V) % 2
            LTV = (LT @ V) % 2
            st_fix = np.all((ST_ @ V) % 2 == V, axis=0)
            globally_nonfinite = not np.array_equal(TS, np.eye(dim, dtype=np.int64))
            for MS in kron_R:
                c1 = np.all((MS @ V) % 2 == LSV, axis=0) & ts_fix
                c1[0] = False  # v = 0 is trivial
                if not c1.any():
                    continue
                for MT in kron_R:
                    good = c1 & np.all((MT @ V) % 2 == LTV, axis=0)
                    k = int(good.sum())
                    if k:
                        hits += k
                        if globally_nonfinite:
                            nontrivial += k
                        bad += int((good & ~st_fix).sum())
    return hits, nontrivial, bad


if __name__ == "__main__":
    ok1, n1 = part1()
    print(f"Part 1: {n1} exact P_22 identities hold: {ok1}")
    ok_ts, ok_st, head = part2()
    print(f"Part 2 (one-sided control): Lam(T)Lam(S)v = v: {ok_ts}; "
          f"Lam(S)Lam(T)v = ev(ST): {ok_st}; head ev(Q) alive: {head}")
    hits, nontriv, bad = part3()
    print(f"Part 3: hypotheses met by {hits} (Lam,M,v) with v != 0, "
          f"{nontriv} with Lam(T)Lam(S) != 1 on H; "
          f"violations of Lam(S)Lam(T)v = v: {bad}")
    good = ok1 and ok_ts and ok_st and head and hits > 0 and nontriv > 0 and bad == 0
    sys.exit(0 if good else 1)
