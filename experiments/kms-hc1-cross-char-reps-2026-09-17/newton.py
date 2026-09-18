#!/usr/bin/env python3
"""Complex representations of Gamma^A2_p (edge A2) or Gamma_p (edge B2) in block normal form,
solved by complex Levenberg-Marquardt with an exact (holomorphic) Jacobian.

Block normal form (see blocksearch.py): V = sum_i E_i, E_i = C^m, B = zeta^i on E_i,
A = X(sA, betaA) monomial, C = G X(sC, betaC) G^-1 with G = diag(g_0..g_{p-1}), g_i in GL_m(C).
Then all relators of <a,b> and <b,c> hold identically.  Unknowns: G.  Equations (as matrix
differences, no inverses of T):
   A2:  T A - A T = 0,  T C - C T = 0,          T = A^-1 C^-1 A C
   B2:  T A - A T = 0,  U A - A U = 0,  U C - C U = 0,   U = T^-1 C^-1 T C
Tangent at G: G -> (I+K) G with K block diagonal, so dC = [K, C] and dC^-1 = [K, C^-1].

For every converged start we record whether R=[B,A] and S=[B,C] commute and whether
(RS)^p = I.  By Malcev, a solution with (RS)^p != I yields a finite image detecting w_p.

Usage: newton.py p m edge trials seed sA sC [betaA|r] [betaC|r]
"""
import sys
import numpy as np

p, m = int(sys.argv[1]), int(sys.argv[2])
edge = sys.argv[3]
trials, seed = int(sys.argv[4]), int(sys.argv[5])
sA = [int(x) for x in sys.argv[6].split(",")]
sC = [int(x) for x in sys.argv[7].split(",")]
bA_arg = sys.argv[8] if len(sys.argv) > 8 else "0"
bC_arg = sys.argv[9] if len(sys.argv) > 9 else "0"
rng = np.random.default_rng(seed)
n = p * m
z = np.exp(2j * np.pi / p)
I = np.eye(n, dtype=complex)


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


def beta(arg):
    if arg == "r":
        return list(rng.integers(0, p, n))
    if arg == "0":
        return [0] * n
    return [int(x) for x in arg.split(",")]


B = np.diag([z ** (j // m) for j in range(n)])
Binv = B.conj()


def blockdiag(blocks):
    G = np.zeros((n, n), dtype=complex)
    for i in range(p):
        G[i * m:(i + 1) * m, i * m:(i + 1) * m] = blocks[i]
    return G


def residual_and_jac(A, Ainv, C, Cinv):
    T = Ainv @ Cinv @ A @ C
    if edge == "A2":
        F = [T @ A - A @ T, T @ C - C @ T]
    else:
        Tinv = Cinv @ Ainv @ C @ A
        U = Tinv @ Cinv @ T @ C
        F = [T @ A - A @ T, U @ A - A @ U, U @ C - C @ U]
    Fv = np.concatenate([f.ravel() for f in F])
    cols = []
    for i in range(p):
        for r in range(m):
            for s in range(m):
                K = np.zeros((n, n), dtype=complex)
                K[i * m + r, i * m + s] = 1
                dC = K @ C - C @ K
                dCi = K @ Cinv - Cinv @ K
                dT = Ainv @ dCi @ A @ C + Ainv @ Cinv @ A @ dC
                if edge == "A2":
                    d = [dT @ A - A @ dT, dT @ C + T @ dC - dC @ T - C @ dT]
                else:
                    dTi = dCi @ Ainv @ C @ A + Cinv @ Ainv @ dC @ A
                    dU = dTi @ Cinv @ T @ C + Tinv @ dCi @ T @ C + Tinv @ Cinv @ dT @ C + Tinv @ Cinv @ T @ dC
                    d = [dT @ A - A @ dT, dU @ A - A @ dU, dU @ C + U @ dC - dC @ U - C @ dU]
                cols.append(np.concatenate([x.ravel() for x in d]))
    return Fv, np.array(cols).T


stats = {"conv": 0, "commuting": 0, "detect": 0, "noconv": 0}
for t in range(trials):
    bA, bC = beta(bA_arg), beta(bC_arg)
    A = normal_form(sA, bA)
    Ainv = np.linalg.matrix_power(A, p - 1)
    XC = normal_form(sC, bC)
    XCinv = np.linalg.matrix_power(XC, p - 1)
    G = blockdiag([np.eye(m) + 0.8 * (rng.standard_normal((m, m)) + 1j * rng.standard_normal((m, m))) for _ in range(p)])
    lam = 1e-2
    ok = False
    for it in range(400):
        Gi = np.linalg.inv(G)
        C, Cinv = G @ XC @ Gi, G @ XCinv @ Gi
        F, J = residual_and_jac(A, Ainv, C, Cinv)
        nf = np.linalg.norm(F) / max(1.0, np.linalg.norm(C))
        if nf < 1e-12:
            ok = True
            break
        JH = J.conj().T
        H = JH @ J
        gvec = JH @ F
        while True:
            try:
                delta = -np.linalg.solve(H + lam * np.eye(H.shape[0]), gvec)
            except np.linalg.LinAlgError:
                lam *= 10
                continue
            K = blockdiag([delta[i * m * m:(i + 1) * m * m].reshape(m, m) for i in range(p)])
            Gn = (I + K) @ G
            try:
                Gni = np.linalg.inv(Gn)
            except np.linalg.LinAlgError:
                lam *= 10
                continue
            Cn, Cni = Gn @ XC @ Gni, Gn @ XCinv @ Gni
            T = Ainv @ Cni @ A @ Cn
            if edge == "A2":
                Fn = np.concatenate([(T @ A - A @ T).ravel(), (T @ Cn - Cn @ T).ravel()])
            else:
                Tinv = Cni @ Ainv @ Cn @ A
                U = Tinv @ Cni @ T @ Cn
                Fn = np.concatenate([(T @ A - A @ T).ravel(), (U @ A - A @ U).ravel(), (U @ Cn - Cn @ U).ravel()])
            if np.linalg.norm(Fn) < np.linalg.norm(F):
                G = Gn
                lam = max(lam / 3, 1e-12)
                break
            lam *= 4
            if lam > 1e8:
                break
        if lam > 1e8:
            break
    Gi = np.linalg.inv(G)
    C = G @ XC @ Gi
    cond = np.linalg.cond(G)
    if not ok or cond > 1e8:
        stats["noconv"] += 1
        print(f"trial {t}: no  res={nf:.1e} it={it} cond={cond:.1e}", flush=True)
        continue
    stats["conv"] += 1
    Cinv = G @ XCinv @ Gi
    R = Binv @ Ainv @ B @ A
    S = Binv @ Cinv @ B @ C
    RS = R @ S
    rsc = np.linalg.norm(R @ S - S @ R) / np.linalg.norm(R)
    wdev = np.linalg.norm(np.linalg.matrix_power(RS, p) - I)
    T = Ainv @ Cinv @ A @ C
    tev = np.round(np.angle(np.linalg.eigvals(T)) / (2 * np.pi / p), 3)
    tag = "COMMUTING" if rsc < 1e-7 else ("DETECT" if wdev > 1e-6 else "noncommuting-but-w=1")
    if rsc < 1e-7:
        stats["commuting"] += 1
    if wdev > 1e-6:
        stats["detect"] += 1
    print(f"trial {t}: CONVERGED it={it} cond={cond:.1e} |[R,S]|={rsc:.2e} |(RS)^p-I|={wdev:.2e} {tag} "
          f"T-args={sorted(set(tev % p))} bA={''.join(map(str, bA))} bC={''.join(map(str, bC))}", flush=True)
    if wdev > 1e-6:
        ev = np.linalg.eigvals(RS)
        print("  args(RS)/(2pi):", np.round(np.sort(np.angle(ev) / (2 * np.pi)), 6), "|ev|:", np.round(np.sort(np.abs(ev)), 5), flush=True)
        np.savez(f"cand_newton_p{p}_m{m}_{edge}_s{seed}_t{t}.npz", A=A, B=B, C=C)
print("STATS", stats, flush=True)
