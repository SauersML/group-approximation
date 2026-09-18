#!/usr/bin/env python3
"""Sanity checks for sse-reductions-need-high-threshold-rank-on-both-sides.

Regular integer-weighted multigraphs M (row sums d), A = M/d, B = (I + A)/2.

  (C1) Rayleigh: <1_S, A 1_S> = e(S)/d = (1 - Phi(S)) s, and e(S) + E(S, S^c) = d s.
  (C2) spectral split: ||f_lo||^2 <= (||f||^2 - <f, B f>) / (1 - theta).
  (C3) threshold rounding: |T xor S| <= 4 ||g - f||^2 and e(T) >= e(S) - 2 d |S \\ T|.
  (C4) window lemma, exhaustive: for every nonempty T, some s-set T' has
       1 - Phi(T') >= (1 - Phi(T)) kappa(|T|), kappa(t) = t/s (t <= s), (s-1)/(t-1) (t > s).
  (C5) greedy Gram--Schmidt on columns of B^t stops with m <= max(2R - 1, 0)
       residuals above tau, when (1 - gamma)^(2t) <= tau^2 / n^2, R = #eig(B) >= 1 - gamma.
  (C6) high part: ||Q f_hi|| <= sqrt(n) theta_hi^(-t) sqrt(tau) ||f_hi|| at the stop.
  (C7) end to end: planted YES graph; the grid on the greedy span finds T with
       rho(T) = (1 - Phi(T)) kappa(|T|) > eta_test; on a NO-like expander no T has
       rho(T) above the true max over s-sets (soundness of the accept rule, exhaustive n small).
  (C8) the parameter inequalities of the proof, exactly/for all L up to 4096.
  (C9) rational certificate soundness toy: d s - e(x) = (1/2) sum M(u,v)(x_u - x_v)^2
       + d sum (x_u - x_u^2) ... identity checked exactly, evaluated on all s-sets.

Run: python3 check_two_sided_rank_gate.py   (exits nonzero on any failure)
"""
import itertools
import math
import sys
from fractions import Fraction

import numpy as np

rng = np.random.default_rng(917)
FAIL = []


def check(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + (" " + detail if detail else ""))
    if not ok:
        FAIL.append(name)


def matching(vertices):
    perm = rng.permutation(vertices)
    return [(int(perm[i]), int(perm[i + 1])) for i in range(0, len(perm) - 1, 2)]


def regular_graph(n, d):
    M = np.zeros((n, n), dtype=np.int64)
    for _ in range(d):
        for u, v in matching(np.arange(n)):
            M[u, v] += 1
            M[v, u] += 1
    return M


def planted_graph(n, s, d, cross):
    """s even, n - s even: d - cross matchings inside S and inside S^c, cross global."""
    M = np.zeros((n, n), dtype=np.int64)
    S = np.arange(s)
    C = np.arange(s, n)
    for _ in range(d - cross):
        for part in (S, C):
            for u, v in matching(part):
                M[u, v] += 1
                M[v, u] += 1
    for _ in range(cross):
        for u, v in matching(np.arange(n)):
            M[u, v] += 1
            M[v, u] += 1
    return M, set(range(s))


def e_in(M, T):
    idx = np.array(sorted(T), dtype=int)
    if len(idx) == 0:
        return 0
    return int(M[np.ix_(idx, idx)].sum())


def one_minus_phi(M, d, T):
    return e_in(M, T) / (d * len(T))


def kappa(t, s):
    return t / s if t <= s else (s - 1) / (t - 1)


# (C1)-(C3)
for trial in range(20):
    n, d = 40, 5
    M = regular_graph(n, d)
    A = M / d
    B = (np.eye(n) + A) / 2
    s = int(rng.integers(2, 20))
    S = set(rng.choice(n, size=s, replace=False).tolist())
    f = np.zeros(n)
    f[list(S)] = 1.0
    eS = e_in(M, S)
    boundary = sum(M[u, v] for u in S for v in range(n) if v not in S)
    ok1 = abs(f @ A @ f - eS / d) < 1e-9 and eS + boundary == d * s
    lam, U = np.linalg.eigh(B)
    theta = float(rng.uniform(0.5, 0.99))
    lo = U[:, lam < theta]
    flo2 = float(np.sum((lo.T @ f) ** 2))
    ok2 = flo2 <= (f @ f - f @ B @ f) / (1 - theta) + 1e-9
    g = f + rng.normal(0, 0.3, size=n)
    T = {v for v in range(n) if g[v] >= 0.5}
    ok3 = len(T ^ S) <= 4 * float((g - f) @ (g - f)) + 1e-9 and e_in(M, T) >= eS - 2 * d * len(S - T)
    if not (ok1 and ok2 and ok3):
        check("C1-C3 trial %d" % trial, False, str((ok1, ok2, ok3)))
        break
else:
    check("C1 Rayleigh, C2 split, C3 rounding (20 random trials)", True)

# (C4) window lemma exhaustive
allok = True
for trial in range(3):
    n, d, s = 12, 3, 4
    M = regular_graph(n, d)
    best = max(one_minus_phi(M, d, set(c)) for c in itertools.combinations(range(n), s))
    for mask in range(1, 1 << n):
        T = {i for i in range(n) if mask >> i & 1}
        rho = one_minus_phi(M, d, T) * kappa(len(T), s)
        if rho > best + 1e-12:
            allok = False
            break
check("C4 window lemma, exhaustive over all T on 3 graphs n=12 s=4", allok)


def greedy_span(B, t, tau, cap):
    n = B.shape[0]
    P = np.linalg.matrix_power(B, t)
    vs = []
    while True:
        W = P.copy()
        for v in vs:
            W -= np.outer(v, (v @ W) / (v @ v))
        res = np.sum(W ** 2, axis=0)
        z = int(np.argmax(res))
        if res[z] <= tau:
            return vs, W, False
        if len(vs) == cap:
            return vs, W, True
        vs.append(W[:, z].copy())


# (C5), (C6)
ok5 = ok6 = True
for trial in range(8):
    n, d = 30, 4
    M = regular_graph(n, d)
    B = (np.eye(n) + M / d) / 2
    gamma = 0.3
    tau = 1e-6
    t = math.ceil(math.log(n / tau) / gamma)
    assert (1 - gamma) ** (2 * t) <= tau ** 2 / n ** 2
    lam, U = np.linalg.eigh(B)
    R = int(np.sum(lam >= 1 - gamma))
    vs, W, above = greedy_span(B, t, tau, 2 * n)
    m = len(vs)
    if m > max(2 * R - 1, 0):
        ok5 = False
    # C6
    theta_hi = 1 - gamma / 8
    Qbasis = np.array(vs).T if vs else np.zeros((n, 0))
    for _ in range(5):
        f = np.zeros(n)
        f[rng.choice(n, size=6, replace=False)] = 1
        hi = U[:, lam >= theta_hi]
        fhi = hi @ (hi.T @ f)
        if Qbasis.shape[1]:
            q, _ = np.linalg.qr(Qbasis)
            Qf = fhi - q @ (q.T @ fhi)
        else:
            Qf = fhi
        bound = math.sqrt(n) * theta_hi ** (-t) * math.sqrt(tau) * np.linalg.norm(fhi)
        if np.linalg.norm(Qf) > bound + 1e-9:
            ok6 = False
check("C5 greedy stop m <= max(2R-1,0) (8 graphs, gamma=0.3, tau=1e-6)", ok5)
check("C6 ||Q f_hi|| <= sqrt(n) theta_hi^-t sqrt(tau) ||f_hi||", ok6)


def grid_decide(M, d, s, vs, h, eta_test):
    n = M.shape[0]
    if not vs:
        return False, None
    psis = []
    for v in vs:
        nv = v @ v
        e = math.floor(math.log(nv / s, 4))
        psis.append(v / 2 ** e)
    Psi = np.array(psis).T
    lev = np.arange(-1, 1 + h / 2, h)
    best = 0.0
    for dvec in itertools.product(lev, repeat=len(vs)):
        g = Psi @ np.array(dvec)
        T = set(np.nonzero(g >= 0.5)[0].tolist())
        if not T:
            continue
        rho = one_minus_phi(M, d, T) * kappa(len(T), s)
        best = max(best, rho)
    return best > eta_test, best


# (C7) end to end, planted YES graph with two blocks
n, s, d = 40, 20, 8
M, S = planted_graph(n, s, d, cross=1)
B = (np.eye(n) + M / d) / 2
gamma, tau = 0.3, 1e-6
t = math.ceil(math.log(n / tau) / gamma)
vs, W, above = greedy_span(B, t, tau, 8)
print("  C7a planted: Phi(S) = %.3f" % (1 - one_minus_phi(M, d, S)))
m = len(vs)
acc, best = grid_decide(M, d, s, vs, 0.25 if m > 2 else 0.09 / math.sqrt(m + 1), 0.05)
check("C7a planted two-block YES graph: greedy span m=%d, grid finds rho=%.3f > eta" % (m, best or 0), acc and not above)

# (C7b) accept rule soundness: best rho over grid never exceeds true max over s-sets (n small)
ok7 = True
for trial in range(3):
    n, d, s = 14, 4, 5
    M = regular_graph(n, d)
    true_best = max(one_minus_phi(M, d, set(c)) for c in itertools.combinations(range(n), s))
    B = (np.eye(n) + M / d) / 2
    t = math.ceil(math.log(n / tau) / gamma)
    vs, W, above = greedy_span(B, t, tau, 3)
    if above or not vs:
        continue
    _, best = grid_decide(M, d, s, vs[:3], 0.5, 0.0)
    if best is not None and best > true_best + 1e-12:
        ok7 = False
check("C7b accept-rule soundness: grid rho <= max over s-sets", ok7)

# (C8) parameter inequalities
ok8 = True
for L in range(0, 4097):
    # log2(sqrt(n) theta^-t sqrt(tau)) upper bound from the proof
    val = L / 2 + math.log2(math.e) * (0.175 * (40 + 7 * L) + 0.125) - 20 - 3 * L
    if not val < math.log2(1 / 100):
        ok8 = False
    if not math.log(2) * (40 + 7 * L) <= 0.7 * (40 + 7 * L):
        ok8 = False
eta = Fraction(1, 800)
lower = Fraction(84, 100) * (Fraction(68, 100) - eta) / Fraction(116, 100)
ok8 = ok8 and lower > eta and float(lower) > 0.49
ok8 = ok8 and all(Fraction(s - 1) / (Fraction(116, 100) * s - 1) >= Fraction(84, 100) for s in range(100, 5000))
ok8 = ok8 and (Fraction(9, 100) + Fraction(1, 100) + Fraction(1, 10)) == Fraction(1, 5)
ok8 = ok8 and 4 * Fraction(1, 25) == Fraction(16, 100)
check("C8 parameter inequalities (L <= 4096, s in [100, 5000), eta = 1/800)", ok8, "rho lower bound %.4f" % float(lower))


# (C9) exact certificate identity for c = 1 and its soundness on s-sets
def poly_add(p, q, c=1):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + c * v
        if r[k] == 0:
            del r[k]
    return r


def mono(*vars_):
    return tuple(sorted(vars_))


n, d, s = 8, 3, 3
M = regular_graph(n, d)
# LHS: d*s - e(x)
lhs = {(): Fraction(d * s)}
for u in range(n):
    for v in range(n):
        if M[u, v]:
            lhs = poly_add(lhs, {mono(u, v): Fraction(int(M[u, v]))}, -1)
# RHS: (1/2) sum M(u,v)(x_u - x_v)^2 + d * sum_u (x_u - x_u^2) * (-1) ... + d * (s - sum x)
rhs = {}
for u in range(n):
    for v in range(n):
        if M[u, v]:
            w = Fraction(int(M[u, v]), 2)
            sq = {mono(u, u): 1, mono(v, v): 1, mono(u, v): -2} if u != v else {}
            rhs = poly_add(rhs, {k: w * c for k, c in sq.items()})
for u in range(n):
    # ideal term a_u (x_u^2 - x_u) with a_u = -d
    rhs = poly_add(rhs, {mono(u, u): Fraction(-d), mono(u): Fraction(d)})
# linear constraint b (sum x - s) with b = -d
rhs = poly_add(rhs, {mono(u): Fraction(-d) for u in range(n)})
rhs = poly_add(rhs, {(): Fraction(d * s)})
ok9 = lhs == rhs
for c in itertools.combinations(range(n), s):
    if e_in(M, set(c)) > d * s:
        ok9 = False
check("C9 exact rational certificate identity d s - e(x) = SOS + ideal, sound on s-sets", ok9)

if FAIL:
    print("FAILED:", FAIL)
    sys.exit(1)
print("ALL PASS")
