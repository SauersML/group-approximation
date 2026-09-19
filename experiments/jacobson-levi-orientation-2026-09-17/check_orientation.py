#!/usr/bin/env python3
"""Right-Levi orientation dichotomy for the double parabolic of EL_4(J).

J = F_2<S,T | TS=1>, Q = 1 - ST.  Elements of

    P^T = M_2(J) x| (EL_2(J) x EL_2(F_2[T]))  <=  P_{2,2}(J)  <=  EL_4(J)

are triples (g, X, B) for [[g, X], [0, B]], with product

    (g, X, B)(g', X', B') = (g g', g X' + X B', B B').

Claim under test (research/jacobson-t-oriented-double-parabolic-is-lef.md):

    Psi(g, X, B) = [[ Phi_M(g), ev_d(X) ], [ 0, B^tau ]]

where Phi_M is the mirror-glued EL_2(J) model, ev_d(X) evaluates the two
columns of X on e_0..e_{d-1}, and B^tau substitutes the nilpotent down-shift
tau (delta_s -> delta_{s-1}, delta_0 -> 0) for T.  Right multiplication by T
is exact on the window: (x T) e_s = x e_{s-1}.

Test A: random words in the generators multiply like the group.
Test B: injective on the words seen.
Test C: the head x_13(Q) has nontrivial image.
Control D: add the right generator x_43(S), modelled by the truncated
  up-shift sigma (delta_s -> delta_{s+1}); Test A fails (window leaves at s=d-1).
Test E: trap linear algebra.  (i) exhaustive over F_2^2, random over F_2^3:
  M_s commuting with L_s, L_t, L_s v = M_s v, L_t L_s v = v  ==>  L_s L_t v = v.
  (ii) the T-oriented hypotheses (M_t commuting, L_t v = M_t v) do not force it:
  explicit counterexample.
Exit code 0 iff every test passes.
"""
import importlib.util
import itertools
import os
import random
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
W9 = os.path.join(HERE, "..", "jacobson-parabolic-lef-2026-09-17", "check_parabolic_lef.py")
spec = importlib.util.spec_from_file_location("w9", W9)
w9 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(w9)

ZERO, ONE, S, T, Q = w9.ZERO, w9.ONE, w9.S, w9.T, w9.Q
jadd, jmul, mmul = w9.jadd, w9.jmul, w9.mmul
I2 = w9.I2
Z2 = [[ZERO, ZERO], [ZERO, ZERO]]


def madd(A, B):
    return [[jadd(A[r][c], B[r][c]) for c in range(2)] for r in range(2)]


def tmul(x, y):
    """(g,X,B)(g',X',B') = (gg', gX' + XB', BB')."""
    g, X, B = x
    h, Y, C = y
    return (mmul(g, h), madd(mmul(g, Y), mmul(X, C)), mmul(B, C))


def key(x):
    return tuple(tuple(sorted(m[r][c])) for m in x for r in range(2) for c in range(2))


# ---------- the model ----------


def ev2(X, M, d):
    """columns (c, s) -> (X_1c e_s, X_2c e_s), c in {3,4} coded 0,1."""
    return np.hstack([w9.ev((X[0][c], X[1][c]), M, d) for c in range(2)])


def shift_poly(p, d):
    """p in F_2[S,T]-monomials; T -> tau (down-shift, exact), S -> sigma
    (truncated up-shift, used only by the control)."""
    out = np.zeros((d, d), dtype=np.uint8)
    for (i, j) in p:
        m = np.eye(d, dtype=np.uint8)
        for _ in range(j):
            m = w9.mat2mul(np.eye(d, k=1, dtype=np.uint8), m)   # tau: delta_s -> delta_{s-1}
        for _ in range(i):
            m = w9.mat2mul(np.eye(d, k=-1, dtype=np.uint8), m)  # sigma: delta_s -> delta_{s+1}
        out ^= m
    return out


def right_model(B, d):
    R = np.zeros((2 * d, 2 * d), dtype=np.uint8)
    for i in range(2):
        for j in range(2):
            R[i * d:(i + 1) * d, j * d:(j + 1) * d] = shift_poly(B[i][j], d)
    return R


def psi(x, ginv, M, d):
    g, X, B = x
    n1, n2 = 2 * (M + 1), 2 * d
    out = np.zeros((n1 + n2, n1 + n2), dtype=np.uint8)
    out[:n1, :n1] = w9.phi_exact(g, ginv, M, "twist")
    out[:n1, n1:] = ev2(X, M, d)
    out[n1:, n1:] = right_model(B, d)
    return out


def generators(M, d, control=False):
    gens = []
    for a in w9.coeffs(2):
        gens.append(([[ONE, a], [ZERO, ONE]], Z2, I2))
        gens.append(([[ONE, ZERO], [a, ONE]], Z2, I2))
        for r in range(2):
            for c in range(2):
                Y = [[ZERO, ZERO], [ZERO, ZERO]]
                Y[r][c] = a
                gens.append((I2, Y, I2))
    T2 = jmul(T, T)
    for p in (ONE, T, T2, jadd(T, ONE)):
        gens.append((I2, Z2, [[ONE, p], [ZERO, ONE]]))
        gens.append((I2, Z2, [[ONE, ZERO], [p, ONE]]))
    if control:
        gens.append((I2, Z2, [[ONE, ZERO], [S, ONE]]))
    # every generator is an involution in characteristic 2
    return [(x, x[0], psi(x, x[0], M, d)) for x in gens]


# ---------- Tests A, B (and control D) ----------


def run_words(M, d, words, maxlen, seed, control=False):
    rng = random.Random(seed)
    gens = generators(M, d, control)
    n = 2 * (M + 1) + 2 * d
    fails, seen = 0, {}
    for _ in range(words):
        word = [rng.randrange(len(gens)) for _ in range(rng.randint(1, maxlen))]
        if control:
            # force the control generator and a column root into the word
            word += [2 + rng.randrange(4), len(gens) - 1]
        x, ginv, img = (I2, Z2, I2), I2, np.eye(n, dtype=np.uint8)
        for w in word:
            gx, gxinv, gimg = gens[w]
            x = tmul(x, gx)
            ginv = mmul(gxinv, ginv)
            img = w9.mat2mul(img, gimg)
        if not np.array_equal(img, psi(x, ginv, M, d)):
            fails += 1
        k, ib = key(x), img.tobytes()
        if k in seen and seen[k] != ib:
            fails += 1
        seen[k] = ib
    collisions = len(seen) - len(set(seen.values()))
    return fails, len(seen), collisions


def head_image(M, d):
    x = (I2, [[Q, ZERO], [ZERO, ZERO]], I2)
    img = psi(x, I2, M, d)
    return not np.array_equal(img, np.eye(img.shape[0], dtype=np.uint8))


# ---------- Test E: trap linear algebra ----------


def mats(n):
    for bits in itertools.product((0, 1), repeat=n * n):
        yield np.array(bits, dtype=np.uint8).reshape(n, n)


def trap_holds(Ls, Lt, Ms, v):
    """None if hypotheses fail, else whether L_s L_t v = v."""
    mm = w9.mat2mul
    if not (np.array_equal(mm(Ms, Ls), mm(Ls, Ms)) and np.array_equal(mm(Ms, Lt), mm(Lt, Ms))):
        return None
    if not np.array_equal(mm(Ls, v), mm(Ms, v)):
        return None
    if not np.array_equal(mm(Lt, mm(Ls, v)), v):
        return None
    return np.array_equal(mm(Ls, mm(Lt, v)), v)


def test_e(seed=11, samples=200000):
    ms2 = list(mats(2))
    vs2 = [np.array([[a], [b]], dtype=np.uint8) for a in (0, 1) for b in (0, 1) if a or b]
    hyp, bad = 0, 0
    for Ls in ms2:
        for Lt in ms2:
            for Ms in ms2:
                for v in vs2:
                    r = trap_holds(Ls, Lt, Ms, v)
                    if r is not None:
                        hyp += 1
                        bad += (not r)
    rng = np.random.default_rng(seed)
    hyp3, bad3 = 0, 0
    for _ in range(samples):
        Ls, Lt = rng.integers(0, 2, (3, 3), dtype=np.uint8), rng.integers(0, 2, (3, 3), dtype=np.uint8)
        # M_s: a random polynomial in L_s, or random (rarely commutes)
        Ms = rng.integers(0, 2, (3, 3), dtype=np.uint8)
        v = rng.integers(0, 2, (3, 1), dtype=np.uint8)
        if not v.any():
            continue
        r = trap_holds(Ls, Lt, Ms, v)
        if r is not None:
            hyp3 += 1
            bad3 += (not r)
    # T-oriented hypotheses: M_t commutes, L_t v = M_t v, L_t L_s v = v.
    e1 = np.array([[1], [0]], dtype=np.uint8)
    Ls = np.array([[0, 0], [1, 0]], dtype=np.uint8)   # e1 -> e2, e2 -> 0
    Lt = np.array([[0, 1], [0, 0]], dtype=np.uint8)   # e2 -> e1, e1 -> 0
    Mt = np.zeros((2, 2), dtype=np.uint8)
    mm = w9.mat2mul
    cex = (np.array_equal(mm(Lt, e1), mm(Mt, e1))
           and np.array_equal(mm(Lt, mm(Ls, e1)), e1)
           and not np.array_equal(mm(Ls, mm(Lt, e1)), e1))
    return hyp, bad, hyp3, bad3, cex


def main():
    ok = True
    M, d = 120, 20
    fa, nseen, coll = run_words(M, d, words=300, maxlen=7, seed=7)
    print(f"A/B  P^T words: product failures {fa}, distinct elements {nseen}, collisions {coll}")
    ok &= fa == 0 and coll == 0
    h = head_image(M, d)
    print(f"C    head x_13(Q) nontrivial in model: {h}")
    ok &= h
    fc, nc, _ = run_words(M, d, words=60, maxlen=5, seed=8, control=True)
    print(f"D    control with x_43(S): product failures {fc} of {nc} (expected > 0)")
    ok &= fc > 0
    hyp, bad, hyp3, bad3, cex = test_e()
    print(f"E(i) F_2^2 exhaustive: {hyp} hypothesis tuples, {bad} violate the trap")
    print(f"E(i) F_2^3 random:     {hyp3} hypothesis tuples, {bad3} violate the trap")
    print(f"E(ii) T-oriented counterexample valid: {cex}")
    ok &= bad == 0 and bad3 == 0 and hyp > 0 and hyp3 > 0 and cex
    print("ALL PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
