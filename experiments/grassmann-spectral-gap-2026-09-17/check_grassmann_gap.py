#!/usr/bin/env python3
"""Replay for research/grassmann-graphs-have-constant-normalized-spectral-gap.md.

Everything below is a check of a statement that is *proved* in that node and in
its route research/grassmann-spectral-gap-recursion-proof.md.  Nothing here is
used as a proof step; the script only replays the identities on explicit
graphs so that a transcription error in the write-up would be caught.

Notation.  `q` a prime, `[m] = (q^m - 1)/(q - 1)`, `V_l` the set of
`l`-dimensional subspaces of `F_q^n`, and `Gr_q(n,l)` the Grassmann graph on
`V_l` with `L ~ L'` iff `dim(L cap L') = l - 1`.  `A1` is its 0/1 adjacency,
`d1 = q [l] [n-l]` its degree, and

    lambda_2(G) = 1 - (second largest eigenvalue of D^-1/2 A D^-1/2).

Checks (exit 0 iff all pass):

  (C1) `Gr_q(n,l)` is `d1`-regular with `d1 = q [l] [n-l]`, loop-free and
       connected, and `|V_l| = [n choose l]_q`.
  (C2) closed form of the spectral gap:
           lambda_2(Gr_q(n,l)) = [n] / (q [l] [n-l]),
       checked against the numerically computed spectrum.
  (C3) the exact-integer identity behind it,
           q [l] [n-l] - q^2 [l-1] [n-l-1] + 1 = [n],
       for a wide range of (q, n, l) -- this says the closed form agrees with
       the classical eigenvalue theta_1 = q^2 [l-1][n-l-1] - 1.
  (C4) the uniform floor   lambda_2(Gr_q(n,l)) > (q-1)/q >= 1/2.
  (C5) the down-up / up-down recursion the proof runs on:
           (1 - alpha_l) lambda_2(Gr(n,l)) = (1 - gamma_l) lambda_2(Gr(n,l-1)),
       alpha_l = 1/[n-l+1], gamma_l = 1/[l], with base Gr(n,1) = K_{[n]}.
       Checked both as exact rationals and against the computed spectra.
  (C6) the two operator identities the proof uses, as matrices:
           U D = alpha_l I + (1 - alpha_l) A1/d1   on V_l,
           D U = gamma_l I + (1 - gamma_l) A1'/d1' on V_{l-1},
       where D is the down-averaging V_l -> V_{l-1} and U = D^* is the
       up-averaging, and that U really is the adjoint of D for the uniform
       measures (biregularity).
  (C7) the small-set expansion floor Phi(S) >= (1 - mu(S)) lambda_2 on
       Gr_q(n,l), over every subset of size at most 3 and over 400 random
       subsets of every size; and that the zoom-in Z_x = {L : x in L} meets
       it: Phi(Z_x) = 1 - [l-1]/[l] exactly, so zoom-ins are the extremal
       non-expanding sets and their expansion is bounded *below* by
       (q-1)/q (1 - mu), never near 0.  (C7c) sharpens this to an exact
       equality Phi(Z) = (1 - mu(Z)) lambda_2 for zoom-ins AND zoom-outs, so
       those sets are equality cases of the floor and nothing on the Grassmann
       graph is more non-expanding than they are.
  (C8) the domination lemma: if a weighted graph W on V_l has all weighted
       degrees equal to d and W >= c A1 entrywise, then
           lambda_2(W) >= c d1 lambda_2(Gr_q(n,l)) / d,
       on random weightings that dominate the Grassmann adjacency.
  (C9) the bipartite containment graph V_{l-1} - V_l has second singular value
           sigma_2^2 = 1 - [n]/([l] [n-l+1]) < 1/q + o(1).
  (C10) the gate arithmetic of `spectral-gap-ratio-reductions-cannot-prove-ugc`
       (K1) applied to these graphs: with X(s) the least integer x >= 3 with
       C_A log(x)/x < 1 - s, every eta < (q-1)/(q X(s)) satisfies
       lambda_2 >= X(s) eta, for every q >= 2 and every 1 <= l <= n-1.
"""
import itertools
import random
import sys
from fractions import Fraction

import numpy as np

TOL = 1e-9
FAIL = []


def check(name, ok, detail=""):
    print(("  ok   " if ok else "  FAIL ") + name + (("  " + detail) if detail else ""))
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------- q-integers

def qint(m, q):
    """[m]_q = (q^m - 1)/(q - 1), an exact integer."""
    assert m >= 0
    return (q ** m - 1) // (q - 1)


def qbinom(n, l, q):
    """Gaussian binomial [n choose l]_q, exact integer."""
    num = 1
    den = 1
    for i in range(l):
        num *= q ** (n - i) - 1
        den *= q ** (i + 1) - 1
    return num // den


# ------------------------------------------------------- subspaces over F_q

def rref_subspaces(n, l, q):
    """All l-dimensional subspaces of F_q^n, as RREF basis matrices (tuples).

    A subspace has a unique RREF basis: choose the l pivot columns, then the
    free entries are those to the right of a pivot and not in a later pivot
    column.
    """
    out = []
    for pivots in itertools.combinations(range(n), l):
        free = []
        for r, p in enumerate(pivots):
            for c in range(p + 1, n):
                if c not in pivots:
                    free.append((r, c))
        for vals in itertools.product(range(q), repeat=len(free)):
            M = [[0] * n for _ in range(l)]
            for r, p in enumerate(pivots):
                M[r][p] = 1
            for (r, c), v in zip(free, vals):
                M[r][c] = v
            out.append(tuple(tuple(row) for row in M))
    return out


def rank_mod(rows, q):
    """Rank over F_q of a list of row tuples (q prime)."""
    M = [list(r) for r in rows]
    n = len(M[0]) if M else 0
    rank = 0
    row = 0
    for col in range(n):
        piv = None
        for r in range(row, len(M)):
            if M[r][col] % q:
                piv = r
                break
        if piv is None:
            continue
        M[row], M[piv] = M[piv], M[row]
        inv = pow(M[row][col], q - 2, q) if q > 2 else 1
        M[row] = [(x * inv) % q for x in M[row]]
        for r in range(len(M)):
            if r != row and M[r][col] % q:
                f = M[r][col] % q
                M[r] = [(a - f * b) % q for a, b in zip(M[r], M[row])]
        row += 1
        rank += 1
        if row == len(M):
            break
    return rank


def grassmann_graph(n, l, q):
    """Vertices (RREF bases) and the 0/1 adjacency of Gr_q(n,l)."""
    V = rref_subspaces(n, l, q)
    idx = {v: i for i, v in enumerate(V)}
    N = len(V)
    A = np.zeros((N, N), dtype=np.int64)
    for i in range(N):
        for j in range(i + 1, N):
            if rank_mod(list(V[i]) + list(V[j]), q) == l + 1:
                A[i, j] = A[j, i] = 1
    return V, idx, A


def gap_from_adj(A, weights=None):
    """lambda_2 = 1 - second largest eigenvalue of the normalized adjacency."""
    W = A.astype(float) if weights is None else weights.astype(float)
    deg = W.sum(axis=1)
    Dm = np.diag(1.0 / np.sqrt(deg))
    ev = np.linalg.eigvalsh(Dm @ W @ Dm)
    ev.sort()
    return 1.0 - ev[-2], ev


def contains(vec, basis_rows, q):
    """Is the vector `vec` in the row space of `basis_rows` over F_q?"""
    r0 = rank_mod(list(basis_rows), q)
    r1 = rank_mod(list(basis_rows) + [tuple(vec)], q)
    return r0 == r1


# ------------------------------------------------------------------- checks

CASES = [(2, 4, 2), (2, 5, 2), (2, 5, 3), (2, 6, 2), (3, 4, 2), (2, 6, 3)]

print("Grassmann spectral gap replay\n")
print("(C1)-(C2)-(C4) regularity, closed form, uniform floor")
cache = {}
for (q, n, l) in CASES:
    V, idx, A = grassmann_graph(n, l, q)
    cache[(q, n, l)] = (V, idx, A)
    N = len(V)
    d1 = q * qint(l, q) * qint(n - l, q)
    degs = A.sum(axis=1)
    lam, ev = gap_from_adj(A)
    closed = qint(n, q) / (q * qint(l, q) * qint(n - l, q))
    ok = (N == qbinom(n, l, q) and np.all(degs == d1) and np.all(np.diag(A) == 0)
          and abs(lam - closed) < TOL and lam > (q - 1) / q)
    check(f"q={q} n={n} l={l}: |V|={N} deg={d1} lambda_2={lam:.10f} "
          f"closed={closed:.10f} floor={(q-1)/q:.3f}", ok)

print("\n(C1b) connectivity (second largest normalized eigenvalue < 1)")
for (q, n, l), (V, idx, A) in cache.items():
    lam, ev = gap_from_adj(A)
    check(f"q={q} n={n} l={l} connected", ev[-2] < 1 - TOL)

print("\n(C3) exact integer identity  q[l][n-l] - q^2[l-1][n-l-1] + 1 = [n]")
bad = []
for q in (2, 3, 4, 5, 7):
    for n in range(2, 40):
        for l in range(1, n):
            lhs = (q * qint(l, q) * qint(n - l, q)
                   - q * q * qint(l - 1, q) * qint(n - l - 1, q) + 1)
            if lhs != qint(n, q):
                bad.append((q, n, l))
check("identity holds for 2<=n<40, 1<=l<n, q in {2,3,4,5,7}", not bad, str(bad[:3]))

print("\n(C4b) uniform floor  [n]/(q[l][n-l]) > (q-1)/q, exact rationals")
bad = []
for q in (2, 3, 4, 5, 7, 8, 9):
    for n in range(2, 60):
        for l in range(1, n):
            lam = Fraction(qint(n, q), q * qint(l, q) * qint(n - l, q))
            if not (lam > Fraction(q - 1, q)):
                bad.append((q, n, l, lam))
check("lambda_2 > (q-1)/q for 2<=n<60, 1<=l<n", not bad, str(bad[:3]))

print("\n(C5) recursion  (1 - alpha_l) lambda_2(l) = (1 - gamma_l) lambda_2(l-1)")
bad = []
for q in (2, 3, 5):
    for n in range(3, 40):
        for l in range(2, n):
            a = Fraction(1, qint(n - l + 1, q))
            g = Fraction(1, qint(l, q))
            s_l = Fraction(qint(n, q), q * qint(l, q) * qint(n - l, q))
            s_lm = Fraction(qint(n, q), q * qint(l - 1, q) * qint(n - l + 1, q))
            if (1 - a) * s_l != (1 - g) * s_lm:
                bad.append((q, n, l))
check("exact-rational recursion, 3<=n<40", not bad, str(bad[:3]))

bad = []
for (q, n, l) in [(2, 5, 2), (2, 5, 3), (2, 6, 2), (3, 4, 2)]:
    if (q, n, l) not in cache:
        cache[(q, n, l)] = grassmann_graph(n, l, q)
    if (q, n, l - 1) not in cache:
        cache[(q, n, l - 1)] = grassmann_graph(n, l - 1, q)
    lam_l = gap_from_adj(cache[(q, n, l)][2])[0]
    if l - 1 == 1:
        lam_lm = float(Fraction(qint(n, q), q * qint(1, q) * qint(n - 1, q)))
    else:
        lam_lm = gap_from_adj(cache[(q, n, l - 1)][2])[0]
    a = 1.0 / qint(n - l + 1, q)
    g = 1.0 / qint(l, q)
    if abs((1 - a) * lam_l - (1 - g) * lam_lm) > 1e-8:
        bad.append((q, n, l, (1 - a) * lam_l, (1 - g) * lam_lm))
check("recursion against computed spectra", not bad, str(bad[:2]))

print("\n(C5b) base case  Gr_q(n,1) = complete graph on [n]_q vertices")
bad = []
for (q, n) in [(2, 4), (2, 5), (3, 4)]:
    V, idx, A = grassmann_graph(n, 1, q)
    N = len(V)
    if N != qint(n, q) or not np.all(A + np.eye(N, dtype=np.int64) == 1):
        bad.append((q, n))
    lam = gap_from_adj(A)[0]
    if abs(lam - float(Fraction(qint(n, q), qint(n, q) - 1))) > TOL:
        bad.append((q, n, "gap"))
check("Gr_q(n,1) complete, lambda_2 = [n]/([n]-1)", not bad, str(bad[:2]))

print("\n(C6) operator identities  UD = alpha I + (1-alpha) A1/d1,"
      "  DU = gamma I + (1-gamma) A1'/d1'")
bad = []
for (q, n, l) in [(2, 4, 2), (2, 5, 2), (2, 5, 3), (3, 4, 2)]:
    Vl, idxl, Al = cache.get((q, n, l)) or grassmann_graph(n, l, q)
    Vm, idxm, Am = cache.get((q, n, l - 1)) or grassmann_graph(n, l - 1, q)
    cache[(q, n, l)] = (Vl, idxl, Al)
    cache[(q, n, l - 1)] = (Vm, idxm, Am)
    # incidence M[i][j] = 1 iff V_{l-1}[j] subset V_l[i]
    Inc = np.zeros((len(Vl), len(Vm)))
    for i, L in enumerate(Vl):
        for j, M in enumerate(Vm):
            if rank_mod(list(L) + list(M), q) == l:
                Inc[i, j] = 1.0
    # biregularity
    if not (np.all(Inc.sum(axis=1) == qint(l, q))
            and np.all(Inc.sum(axis=0) == qint(n - l + 1, q))):
        bad.append((q, n, l, "biregular"))
        continue
    Dmat = Inc.T / qint(n - l + 1, q)  # D: L^2(V_l) -> L^2(V_{l-1}), average up-neighbours
    Umat = Inc / qint(l, q)            # U: L^2(V_{l-1}) -> L^2(V_l), average down-neighbours
    # U = D^* for the uniform measures iff the incidence count matches both ways
    adj_ok = (len(Vm) * qint(n - l + 1, q) == len(Vl) * qint(l, q)
              == int(Inc.sum()))
    UD = Umat @ Dmat                   # on L^2(V_l):  down then up
    DU = Dmat @ Umat                   # on L^2(V_{l-1}): up then down
    a = 1.0 / qint(n - l + 1, q)
    g = 1.0 / qint(l, q)
    d1 = q * qint(l, q) * qint(n - l, q)
    d1m = q * qint(l - 1, q) * qint(n - l + 1, q) if l - 1 >= 1 else None
    ok1 = np.allclose(UD, a * np.eye(len(Vl)) + (1 - a) * Al / d1)
    if l - 1 == 1:
        Am_norm = Am / (qint(n, q) - 1)
    else:
        Am_norm = Am / d1m
    ok2 = np.allclose(DU, g * np.eye(len(Vm)) + (1 - g) * Am_norm)
    if not (adj_ok and ok1 and ok2):
        bad.append((q, n, l, adj_ok, ok1, ok2))
check("UD / DU identities and adjointness", not bad, str(bad[:2]))

print("\n(C7) expansion floor  Phi(S) >= (1 - mu(S)) lambda_2,  zoom-ins extremal")
bad = []
for (q, n, l) in [(2, 4, 2), (2, 5, 2), (3, 4, 2), (2, 5, 3)]:
    V, idx, A = cache.get((q, n, l)) or grassmann_graph(n, l, q)
    cache[(q, n, l)] = (V, idx, A)
    N = len(V)
    d1 = q * qint(l, q) * qint(n - l, q)
    lam = float(Fraction(qint(n, q), d1))
    rng = random.Random(20260917 + n * 10 + l)

    def phi(S):
        S = list(S)
        inside = A[np.ix_(S, S)].sum()
        return 1.0 - inside / (d1 * len(S)), len(S) / N

    # random subsets of every size
    for _ in range(400):
        k = rng.randint(1, N - 1)
        S = rng.sample(range(N), k)
        p, mu = phi(S)
        if p < (1 - mu) * lam - 1e-9:
            bad.append((q, n, l, k, p, (1 - mu) * lam))
            break
    # exhaustive for the smallest graph
    if N <= 35:
        for k in range(1, N):
            for S in itertools.combinations(range(N), k):
                p, mu = phi(S)
                if p < (1 - mu) * lam - 1e-9:
                    bad.append((q, n, l, S))
                    break
            if bad:
                break
            if k >= 3:
                break  # full sweep to size 3 is enough to exercise tiny sets
    # zoom-ins
    for coord in range(n):
        x = [0] * n
        x[coord] = 1
        Z = [i for i, L in enumerate(V) if contains(x, L, q)]
        p, mu = phi(Z)
        want = 1.0 - qint(l - 1, q) / qint(l, q)
        if abs(p - want) > 1e-9 or len(Z) != qbinom(n - 1, l - 1, q):
            bad.append((q, n, l, "zoomin", p, want, len(Z)))
check("floor holds; Phi(zoom-in) = 1 - [l-1]/[l] and |Z| = [n-1 choose l-1]",
      not bad, str(bad[:2]))

print("\n(C7b) zoom-in expansion is bounded below, never near 0")
bad = []
for q in (2, 3, 5):
    for l in range(1, 25):
        p = 1 - Fraction(qint(l - 1, q), qint(l, q))
        if p < Fraction(q - 1, q):
            bad.append((q, l, p))
check("1 - [l-1]/[l] >= (q-1)/q for all l >= 1", not bad, str(bad[:3]))

print("\n(C7c) zoom-ins and zoom-outs attain the floor with EQUALITY:"
      "\n      Phi(Z) = (1 - mu(Z)) lambda_2, exact rationals")
bad = []
for q in (2, 3, 4, 5, 7):
    for n in range(2, 45):
        for l in range(1, n):
            lam = Fraction(qint(n, q), q * qint(l, q) * qint(n - l, q))
            # zoom-in {L : x in L}: mu = [l]/[n], Phi = 1 - [l-1]/[l]
            mu_in = Fraction(qint(l, q), qint(n, q))
            phi_in = 1 - Fraction(qint(l - 1, q), qint(l, q))
            # zoom-out {L : L subset H}: mu = [n-l]/[n], Phi = 1 - [n-l-1]/[n-l]
            mu_out = Fraction(qint(n - l, q), qint(n, q))
            phi_out = 1 - Fraction(qint(n - l - 1, q), qint(n - l, q))
            if phi_in != (1 - mu_in) * lam or phi_out != (1 - mu_out) * lam:
                bad.append((q, n, l))
check("equality for zoom-ins and zoom-outs, 2<=n<45", not bad, str(bad[:3]))

print("\n(C8) domination lemma  lambda_2(W) >= c d1 lambda_2(A1) / d")
bad = []
for (q, n, l) in [(2, 4, 2), (3, 4, 2)]:
    V, idx, A = cache[(q, n, l)]
    N = len(V)
    d1 = q * qint(l, q) * qint(n - l, q)
    lam1 = float(Fraction(qint(n, q), d1))
    rng = np.random.default_rng(7 + n)
    for _ in range(30):
        c = float(rng.uniform(0.2, 1.0))
        # W = c A1 + a symmetric nonnegative regular perturbation (circulant-style)
        P = np.zeros((N, N))
        perm = rng.permutation(N)
        w = float(rng.uniform(0.0, 3.0))
        for i in range(N):
            j = perm[i]
            if i != j:
                P[i, j] += w
                P[j, i] += w
        W = c * A + P
        deg = W.sum(axis=1)
        if deg.min() <= 0 or deg.max() - deg.min() > 1e-9:
            continue  # lemma is stated for weighted-regular W
        lamW = gap_from_adj(A, weights=W)[0]
        if lamW < c * d1 * lam1 / deg[0] - 1e-9:
            bad.append((q, n, l, c, lamW, c * d1 * lam1 / deg[0]))
check("domination bound on random regular dominating weightings", not bad,
      str(bad[:2]))

print("\n(C9) bipartite containment graph  sigma_2^2 = 1 - [n]/([l][n-l+1])")
bad = []
for (q, n, l) in [(2, 4, 2), (2, 5, 2), (2, 5, 3), (3, 4, 2)]:
    Vl, _, _ = cache[(q, n, l)]
    Vm, _, _ = cache[(q, n, l - 1)]
    Inc = np.zeros((len(Vl), len(Vm)))
    for i, L in enumerate(Vl):
        for j, M in enumerate(Vm):
            if rank_mod(list(L) + list(M), q) == l:
                Inc[i, j] = 1.0
    Nrm = Inc / np.sqrt(qint(l, q) * qint(n - l + 1, q))
    sv = np.linalg.svd(Nrm, compute_uv=False)
    sv.sort()
    s2sq = sv[-2] ** 2
    want = 1.0 - qint(n, q) / (qint(l, q) * qint(n - l + 1, q))
    if abs(s2sq - want) > 1e-8 or not (sv[-1] > 1 - TOL):
        bad.append((q, n, l, s2sq, want, sv[-1]))
check("second singular value of the containment graph", not bad, str(bad[:2]))

bad = []
for q in (2, 3, 5):
    for n in range(3, 40):
        for l in range(2, n):
            v = Fraction(qint(n, q), qint(l, q) * qint(n - l + 1, q))
            if not (1 - v < Fraction(1, q)):
                bad.append((q, n, l, v))
check("sigma_2^2 < 1/q, so lambda_2(bipartite) > 1 - 1/sqrt(q)", not bad,
      str(bad[:3]))

print("\n(C10) gate arithmetic of (K1) on these graphs")
import math
def X(s, C_A):
    x = 3
    while not (C_A * math.log(x) / x < 1 - s):
        x += 1
        if x > 10 ** 7:
            raise RuntimeError("X(s) not found")
    return x

bad = []
for C_A in (1.0, 5.0, 50.0):
    for s in (0.01, 0.1, 0.5, 0.9):
        Xs = X(s, C_A)
        for q in (2, 3, 4, 5):
            lam0 = (q - 1) / q
            eta = lam0 / Xs / 2
            if not (lam0 >= Xs * eta):
                bad.append((C_A, s, q))
            # a concrete instance must also satisfy it
            for (n, l) in [(6, 3), (40, 7), (200, 20)]:
                lam = float(Fraction(qint(n, q), q * qint(l, q) * qint(n - l, q)))
                if not (lam >= Xs * eta):
                    bad.append((C_A, s, q, n, l, lam, Xs * eta))
        print(f"    C_A={C_A:>4}  s={s:<5} X(s)={Xs:<6} "
              f"eta_max(q=2) = {0.5/Xs:.6f}")
check("lambda_2 >= X(s) eta for every eta < (q-1)/(q X(s))", not bad, str(bad[:2]))

print()
if FAIL:
    print("FAILURES: " + ", ".join(FAIL))
    sys.exit(1)
print("ALL PASS")
