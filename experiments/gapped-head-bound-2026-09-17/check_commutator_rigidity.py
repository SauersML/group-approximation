#!/usr/bin/env python3
"""Checks for jacobson-head-dies-in-gapped-finite-group-models (Lemmas A and B).

Lemma A (commutator trick over F_2).  For D != 1 in GL_d(F_2) and v in Fix(D) \ Im(D-1),
x = 1 + v (x) phi with phi(v) = 0 and phi o (D^-1 - 1) != 0 gives
[D, x] = 1 + v (x) phi(D^-1 - 1), a transvection.  For d >= 5 every D != 1 reaches a
transvection in two commutator steps (first with a non-commuting transvection x').

Lemma B (HS rigidity of GL_d(F_2), d >= 5).  For every unitary rep rho, every D != 1 and
every y:  ||rho(y) - 1||_2 <= 8 sqrt(2) ||rho(D) - 1||_2, i.e. h(y) <= 128 h(D) with
h = ||.-1||_2^2.  Here we test it on permutation modules (vectors, planes, point-hyperplane
flags) of GL_5(F_2), together with the two commutator steps h([D,x]) <= 4 h(D).

Matrices are lists of row bitmasks; everything is exact.
"""
import random
from itertools import combinations

random.seed(20260918)


def matvec(A, v):
    out = 0
    for i, row in enumerate(A):
        if bin(row & v).count("1") & 1:
            out |= 1 << i
    return out


def matmul(A, B):
    d = len(A)
    out = []
    for i in range(d):
        r = 0
        for j in range(d):
            if (A[i] >> j) & 1:
                r ^= B[j]
        out.append(r)
    return out


def ident(d):
    return [1 << i for i in range(d)]


def add(A, B):
    return [a ^ b for a, b in zip(A, B)]


def rank(A):
    rows = [r for r in A]
    rk = 0
    d = len(A)
    for col in range(d):
        piv = None
        for i in range(rk, len(rows)):
            if (rows[i] >> col) & 1:
                piv = i
                break
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and (rows[i] >> col) & 1:
                rows[i] ^= rows[rk]
        rk += 1
    return rk


def inverse(A):
    d = len(A)
    M = [(A[i], 1 << i) for i in range(d)]
    for col in range(d):
        piv = next(i for i in range(col, d) if (M[i][0] >> col) & 1)
        M[col], M[piv] = M[piv], M[col]
        for i in range(d):
            if i != col and (M[i][0] >> col) & 1:
                M[i] = (M[i][0] ^ M[col][0], M[i][1] ^ M[col][1])
    return [m[1] for m in M]


def rand_gl(d):
    while True:
        A = [random.randrange(1 << d) for _ in range(d)]
        if rank(A) == d:
            return A


def transvection(v, phi, d):
    # (1 + v (x) phi) w = w + phi(w) v ; entries delta_ij + v_i phi_j
    return [(1 << i) ^ (phi if (v >> i) & 1 else 0) for i in range(d)]


def comm(A, B):
    return matmul(matmul(A, B), matmul(inverse(A), inverse(B)))


def is_transvection(C):
    d = len(C)
    N = add(C, ident(d))
    return rank(N) == 1 and all(r == 0 for r in matmul(N, N))


def row_functional_compose(phi, M):
    # functional phi o M as a row bitmask: (phi o M)_j = sum_i phi_i M_ij
    out = 0
    for i in range(len(M)):
        if (phi >> i) & 1:
            out ^= M[i]
    return out


def image_space(M, d):
    return {matvec(M, w) for w in range(1 << d)}


def fixed_space(M, d):
    return {w for w in range(1 << d) if matvec(M, w) == w}


def lemma_a_step(D, d):
    """Return (x, [D,x]) per Lemma A, or None if D has no v in Fix \\ Im."""
    I = ident(d)
    Dm1 = add(D, I)
    im = image_space(Dm1, d)
    fix = fixed_space(D, d)
    cands = [v for v in fix if v and v not in im]
    if not cands:
        return None
    v = random.choice(cands)
    Dinv_m1 = add(inverse(D), I)
    phis = [p for p in range(1, 1 << d)
            if bin(p & v).count("1") % 2 == 0 and row_functional_compose(p, Dinv_m1) != 0]
    phi = random.choice(phis)
    x = transvection(v, phi, d)
    C = comm(D, x)
    predicted = transvection(v, row_functional_compose(phi, Dinv_m1), d)
    assert C == predicted, "commutator formula"
    assert is_transvection(C), "commutator is a transvection"
    return x, C


def random_transvection(d):
    while True:
        v = random.randrange(1, 1 << d)
        phi = random.randrange(1, 1 << d)
        if bin(phi & v).count("1") % 2 == 0:
            return transvection(v, phi, d)


def two_step(D, d):
    while True:
        xp = random_transvection(d)
        if matmul(D, xp) != matmul(xp, D):
            break
    E = comm(D, xp)
    assert rank(add(E, ident(d))) <= 2
    res = lemma_a_step(E, d)
    assert res is not None, "d >= 5 guarantees Fix(E) not inside Im(E-1)"
    x, t = res
    return xp, E, x, t


# ---------------- Lemma A on random elements, d = 5, 6, 7 -----------------
for d in (5, 6, 7):
    cnt = 0
    for _ in range(400):
        D = rand_gl(d)
        if D == ident(d):
            continue
        two_step(D, d)
        cnt += 1
    print(f"Lemma A: d={d}: {cnt} random D != 1 reach a transvection in two commutator steps")

# ---------------- permutation modules of GL_5(F_2) -------------------------
d = 5
vectors = list(range(1 << d))
planes = sorted({frozenset({0, a, b, a ^ b}) for a, b in combinations(range(1, 1 << d), 2)},
                key=sorted)
hyper = list(range(1, 1 << d))  # hyperplane = kernel of functional f
flags = [(p, f) for p in range(1, 1 << d) for f in hyper if bin(p & f).count("1") % 2 == 0]


def dual_action(M):
    # functional f -> f o M^{-1}
    Minv = inverse(M)
    return lambda f: row_functional_compose(f, Minv)


def fix_counts(M):
    fv = sum(1 for w in vectors if matvec(M, w) == w)
    fp = sum(1 for P in planes if frozenset(matvec(M, w) for w in P) == P)
    da = dual_action(M)
    ff = sum(1 for (p, f) in flags if matvec(M, p) == p and da(f) == f)
    return fv, fp, ff


mods = [("vectors", len(vectors), 2), ("planes", len(planes), 1), ("flags", len(flags), 1)]


def hs2(M):
    """h(M) = ||rho(M)-1||_2^2 = 2(1 - fix/N) on each permutation module."""
    return [2 * (1 - fc / N) for fc, (_, N, _) in zip(fix_counts(M), mods)]


t0 = transvection(1, 2, d)
ht = hs2(t0)
worst_ratio = [0.0, 0.0, 0.0]
max_ratio_step = [0.0, 0.0, 0.0]
samples = 0
for _ in range(300):
    D = rand_gl(d)
    if D == ident(d):
        continue
    samples += 1
    hD = hs2(D)
    xp, E, x, t = two_step(D, d)
    hE, hT = hs2(E), hs2(t)
    for k in range(3):
        assert hE[k] <= 4 * hD[k] + 1e-12, "first commutator step"
        assert hT[k] <= 4 * hE[k] + 1e-12, "second commutator step"
        assert abs(hT[k] - ht[k]) < 1e-12, "all transvections conjugate"
        y = rand_gl(d)
        hy = hs2(y)[k]
        assert hy <= 128 * hD[k] + 1e-12, "Lemma B"
        worst_ratio[k] = max(worst_ratio[k], hy / hD[k])
        if hD[k] > 0:
            max_ratio_step[k] = max(max_ratio_step[k], ht[k] / hD[k])

for k, (name, N, orbits) in enumerate(mods):
    N0 = orbits
    floor = 0.5 * (N - N0) / N  # Lemma B floor for h(t) = 4 rank/N >= (1/2)(N-N0)/N
    assert ht[k] >= floor - 1e-12, "transvection floor"
    print(f"GL_5(F_2) on {name:7s} (N={N:4d}): h(t)={ht[k]:.4f} >= floor {floor:.4f};"
          f" max sampled h(y)/h(D) = {worst_ratio[k]:.3f} <= 128;"
          f" max sampled h(t)/h(D) = {max_ratio_step[k]:.3f} <= 16")
print(f"all checks passed ({samples} sampled D)")
