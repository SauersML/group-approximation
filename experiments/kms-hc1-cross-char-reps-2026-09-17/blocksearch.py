#!/usr/bin/env python3
"""Complex representations of Gamma_p (B2 edge) or Gamma^A2_p (A2 edge) in block normal form.

Any complex representation decomposes V into B-eigenspaces E_i (B = zeta^i on E_i).  Since
R=[B,A] is central in <A,B>, A maps E_i cap V_k(R) to E_{i+k}.  We take E_i = C^m for all i and
the normal form
    X(s,beta): e_{i,k} -> e_{i+s_k,k}  if s_k != 0,   e_{i,k} -> beta_{i,k} e_{i,k} if s_k == 0,
with beta^p = 1.  Then [B,X] = diag(zeta^{s_k}) commutes with B and X, and X^p = I.
A = X(sA,betaA),  C = g X(sC,betaC) g^-1 with g block diagonal (commutes with B).
So every relator of <a,b> and <b,c> holds identically; the least-squares residual is only the
<a,c> vertex relators.  By Malcev, any solution with (RS)^p != I gives a finite image detecting w_p.

Usage: blocksearch.py p m edge(A2|B2) trials seed sA sC [betaA] [betaC] [push]
   push (float, default 0): if nonzero, add the residual tr([R,S]) - (n - push) to steer away from commuting R,S.
   sA, sC: comma separated shifts (length m); beta: comma separated exponents, length p*m, or 'r' random.
"""
import sys
import numpy as np
from scipy.optimize import least_squares

p, m = int(sys.argv[1]), int(sys.argv[2])
edge = sys.argv[3]
trials, seed = int(sys.argv[4]), int(sys.argv[5])
sA = [int(x) for x in sys.argv[6].split(",")]
sC = [int(x) for x in sys.argv[7].split(",")]
rng = np.random.default_rng(seed)
n = p * m
z = np.exp(2j * np.pi / p)
I = np.eye(n)
inv = np.linalg.inv


def idx(i, k):
    return (i % p) * m + k


def normal_form(s, bexp):
    X = np.zeros((n, n), dtype=complex)
    for i in range(p):
        for k in range(m):
            if s[k] % p:
                X[idx(i + s[k], k), idx(i, k)] = 1
            else:
                X[idx(i, k), idx(i, k)] = z ** bexp[idx(i, k)]
    return X


def parse_beta(arg):
    if arg is None or arg == "r":
        return None
    if arg == "0":
        return [0] * n
    return [int(x) for x in arg.split(",")]


bA_fixed = parse_beta(sys.argv[8] if len(sys.argv) > 8 else "0")
bC_fixed = parse_beta(sys.argv[9] if len(sys.argv) > 9 else "0")
push = float(sys.argv[10]) if len(sys.argv) > 10 else 0.0
B = np.diag([z ** (j // m) for j in range(n)])


def cm(x, y):
    return inv(x) @ inv(y) @ x @ y


def build(v, XA, XC):
    c = v[: p * m * m] + 1j * v[p * m * m:]
    g = np.zeros((n, n), dtype=complex)
    for i in range(p):
        g[i * m:(i + 1) * m, i * m:(i + 1) * m] = c[i * m * m:(i + 1) * m * m].reshape(m, m)
    return XA, g @ XC @ inv(g)


def rels(A, C):
    T = cm(A, C)
    if edge == "A2":
        return [cm(T, A), cm(T, C)]
    U = cm(T, C)
    return [cm(T, A), cm(U, A), cm(U, C)]


found = []
for t in range(trials):
    bA = bA_fixed if bA_fixed is not None else list(rng.integers(0, p, n))
    bC = bC_fixed if bC_fixed is not None else list(rng.integers(0, p, n))
    XA, XC = normal_form(sA, bA), normal_form(sC, bC)

    def res(v):
        A, C = build(v, XA, XC)
        try:
            o = np.concatenate([(X - I).ravel() for X in rels(A, C)])
        except np.linalg.LinAlgError:
            o = np.full(len(rels(XA, XA)) * n * n, 1e3, dtype=complex)
        c = v[: p * m * m] + 1j * v[p * m * m:]
        dets = [np.linalg.det(c[i * m * m:(i + 1) * m * m].reshape(m, m)) - 1 for i in range(p)]
        o = np.concatenate([o, 0.1 * np.array(dets)])
        if push:
            Rr, Ss = cm(B, A), cm(B, C)
            o = np.concatenate([o, [np.trace(cm(Rr, Ss)) - (n - push)]])
        return np.concatenate([o.real, o.imag])

    g0 = np.concatenate([(np.eye(m) + 0.7 * (rng.standard_normal((m, m)) + 1j * rng.standard_normal((m, m)))).ravel()
                         for _ in range(p)])
    v0 = np.concatenate([g0.real, g0.imag])
    try:
        sol = least_squares(res, v0, method="lm", max_nfev=3000, xtol=1e-15, ftol=1e-15, gtol=1e-15)
    except Exception as e:  # noqa: BLE001
        print(f"trial {t}: error {e}", flush=True)
        continue
    r = np.linalg.norm(res(sol.x))
    A, C = build(sol.x, XA, XC)
    R, S = cm(B, A), cm(B, C)
    RS = R @ S
    ev = np.linalg.eigvals(RS)
    wdev = np.linalg.norm(np.linalg.matrix_power(RS, p) - I)
    rsc = np.linalg.norm(R @ S - S @ R)
    acdev = np.linalg.norm(cm(A, C) - I)
    tag = "CONVERGED" if r < 1e-9 else "no"
    print(f"trial {t}: {tag} res={r:.1e} |[A,C]-I|={acdev:.3f} |[R,S]|={rsc:.3e} |(RS)^p-I|={wdev:.3e} "
          f"|ev|max={np.abs(ev).max():.4f} bA={''.join(map(str,bA))} bC={''.join(map(str,bC))}", flush=True)
    if r < 1e-9 and wdev > 1e-6:
        print("  DETECTION CANDIDATE eigenvalues RS:", np.round(ev, 5), flush=True)
        # independent check of all ten relators of Gamma_p (or the nine of Gamma^A2_p)
        ab, bc, ac = cm(A, B), cm(B, C), cm(A, C)
        allrel = [np.linalg.matrix_power(X, p) for X in (A, B, C)] + [cm(ab, A), cm(ab, B), cm(bc, B), cm(bc, C)] + rels(A, C)
        print("  max relator deviation:", max(np.linalg.norm(X - I) for X in allrel),
              " args(RS)/(2pi):", np.round(np.sort(np.angle(ev) / (2 * np.pi)), 6), flush=True)
        np.savez(f"cand_p{p}_m{m}_{edge}_seed{seed}_t{t}.npz", A=A, B=B, C=C)
