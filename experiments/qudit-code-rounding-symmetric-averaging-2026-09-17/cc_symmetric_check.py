#!/usr/bin/env python3
"""Checks for the all-primes code-constraint rounding factor gamma_d = 1 + 1/sqrt(d).

(a) Pair inequality.  For every pair of stabilizer code projectors P, Q whose compression PQP has
    nonzero spectrum {r} with 0 < r < 1, verify the operator inequality
        PQ + QP - PQP - QPQ  <=  (sqrt r - r) (P + Q).
(b) Rounding.  Run the proof's rounding on random H = sum_a w_a (I - Pi_a): in the current code space
    take a top eigenvector psi, compute for every nontrivial term R the leak
        Leak_R = sum_a w_a Re <psi| Q_R Q_a (I - Q_R) |psi>,  M_R = <psi|Q_R|psi>,  L_R = sum_a w_a (1 - r_aR),
    verify the averaged inequality sum_R w_R (Leak_R - kappa M_R L_R) <= 0 (kappa = 1/(1+sqrt d)),
    post-select on an R with M_R > 0 and Leak_R <= kappa M_R L_R, compress the instance, recurse.
    Report the worst F(phi)/lambda_min(H) against gamma_d.
Works for every prime d (d = 2 uses D(a,b) = i^(ab) X^a Z^b).
Run: nice -n 10 timeout 1200 python3 cc_symmetric_check.py d n trials seed"""
import sys, itertools
import numpy as np

d, n, T, seed = map(int, sys.argv[1:5])
rng = np.random.default_rng(seed); D = d ** n
kappa = 1 / (1 + np.sqrt(d)); gamma = 1 + 1 / np.sqrt(d)
TOL = 1e-8

def weyl_mats():
    w = np.exp(2j * np.pi / d)
    X = np.roll(np.eye(d), 1, axis=0); Z = np.diag(w ** np.arange(d))
    one = []
    for a in range(d):
        for b in range(d):
            ph = (1j) ** (a * b) if d == 2 else w ** ((pow(2, -1, d) * a * b) % d)
            one.append(ph * np.linalg.matrix_power(X, a) @ np.linalg.matrix_power(Z, b))
    mats = []
    for combo in itertools.product(range(d * d), repeat=n):
        if all(c == 0 for c in combo):
            continue
        M = np.eye(1)
        for c in combo:
            M = np.kron(M, one[c])
        mats.append(M)
    return mats

def key(P):
    return tuple(np.round(P.real, 6).ravel() + 0.0) + tuple(np.round(P.imag, 6).ravel() + 0.0)

def code_projectors():
    """all nontrivial code projectors Pi_S: products of commuting eigenprojectors of Weyl operators."""
    w = np.exp(2j * np.pi / d); mats = weyl_mats()
    eig = []
    for g in mats:
        for m in range(d):
            P = sum(w ** (-m * k) * np.linalg.matrix_power(g, k) for k in range(d)) / d
            eig.append(P)
    seen = {}
    frontier = [np.eye(D, dtype=complex)]
    for level in range(n):
        new = []
        for P in frontier:
            for E in eig:
                if not np.allclose(E @ P, P @ E):
                    continue
                R = E @ P
                tr = np.real(np.trace(R))
                if tr < 0.5 or abs(tr - np.real(np.trace(P))) < 0.5:
                    continue
                k = key(R)
                if k not in seen:
                    seen[k] = R; new.append(R)
        frontier = new
    return list(seen.values())

projs = code_projectors()
print(f"d={d} n={n} code projectors={len(projs)} kappa={kappa:.6f} gamma={gamma:.6f}", flush=True)

def principal_r(P, Q):
    ev = np.linalg.eigvalsh(P @ Q @ P)
    nz = ev[ev > TOL]
    if len(nz) == 0:
        return 0.0, True
    return nz[-1], np.allclose(nz, nz[-1], atol=1e-7)

# (a) pair inequality
pairs = list(itertools.combinations(range(len(projs)), 2))
if len(pairs) > 20000:
    pairs = [pairs[i] for i in rng.choice(len(pairs), 20000, replace=False)]
worst_pair = -np.inf; checked = 0
for i, j in pairs:
    P, Q = projs[i], projs[j]
    r, equal = principal_r(P, Q)
    assert equal, "compression spectrum not constant"
    if r < TOL or r > 1 - TOL:
        continue
    X = P @ Q + Q @ P - P @ Q @ P - Q @ P @ Q - (np.sqrt(r) - r) * (P + Q)
    worst_pair = max(worst_pair, np.linalg.eigvalsh((X + X.conj().T) / 2)[-1]); checked += 1
print(f"(a) pairs with 0<r<1 checked={checked}, max eigenvalue of PQ+QP-PQP-QPQ-(sqrt r-r)(P+Q) = {worst_pair:.2e}", flush=True)

def top_vec(K, P0):
    w_, V = np.linalg.eigh(P0); B = V[:, w_ > 0.5]
    ev, U = np.linalg.eigh(B.conj().T @ K @ B)
    return B @ U[:, -1]

worst = 0.0; worst_step = -np.inf; worst_avg = -np.inf
for trial in range(T):
    k = int(rng.integers(2, min(8, len(projs) + 1))); idx = rng.choice(len(projs), size=k, replace=False)
    w0 = rng.exponential(size=k) if trial % 2 else np.ones(k)
    terms = [(w0[a], projs[idx[a]]) for a in range(k)]
    W = w0.sum(); K0 = sum(wa * Qa for wa, Qa in terms)
    lam_min = W - np.linalg.eigvalsh(K0)[-1]
    P0 = np.eye(D, dtype=complex); const = 0.0      # F = const + sum w (1 - <Q>) on range P0
    while True:
        rk0 = np.real(np.trace(P0))
        nontriv = [a for a, (wa, Qa) in enumerate(terms)
                   if wa > TOL and 0.5 < np.real(np.trace(Qa)) < rk0 - 0.5]
        if rk0 < 1.5 or not nontriv:
            break
        K = sum(wa * Qa for wa, Qa in terms)
        psi = top_vec(K, P0)
        best = None; avg = 0.0
        for R in nontriv:
            wR, P = terms[R]; M = np.real(psi.conj() @ P @ psi)
            leak = 0.0; L = 0.0
            for a, (wa, Qa) in enumerate(terms):
                leak += wa * np.real(psi.conj() @ P @ Qa @ (psi - P @ psi))
                ra, _ = principal_r(P, Qa) if np.real(np.trace(Qa)) > 0.5 else (1.0, True)
                if np.allclose(P @ Qa, Qa @ P):
                    ra = 1.0
                L += wa * (1 - ra)
            avg += wR * (leak - kappa * M * L)
            if M > TOL:
                score = leak / M - kappa * L
                if best is None or score < best[0]:
                    best = (score, R, M, leak, L)
        worst_avg = max(worst_avg, avg)
        if best is None:
            break
        worst_step = max(worst_step, best[0])
        _, R, M, leak, L = best
        P = terms[R][1]
        new_terms = []
        for wa, Qa in terms:
            PQP = P @ Qa @ P
            ra, _ = principal_r(P, Qa) if np.real(np.trace(Qa)) > 0.5 else (1.0, True)
            if ra < TOL:                        # P Q P = 0: term is violated on range P
                const += wa; continue
            if np.allclose(P @ Qa, Qa @ P):
                ra = 1.0
            const += wa * (1 - ra)
            new_terms.append((wa * ra, PQP / ra))
        terms = new_terms; P0 = P
    # any stabilizer state in P0: all terms trivial there, F constant; evaluate on a basis vector of P0
    K = sum(wa * Qa for wa, Qa in terms) if terms else np.zeros((D, D))
    vals, V = np.linalg.eigh(P0); v = V[:, -1]
    F_phi = const + sum(wa for wa, _ in terms) - np.real(v.conj() @ K @ v)
    ratio = F_phi / lam_min if lam_min > 1e-9 else (0.0 if F_phi < 1e-9 else np.inf)
    worst = max(worst, ratio)
print(f"(b) trials={T}: max over steps of sum_R w_R(Leak_R - kappa M_R L_R) = {worst_avg:.2e}; "
      f"max chosen Leak_R/M_R - kappa L_R = {worst_step:.2e}; worst F(phi)/lambda_min = {worst:.6f} (gamma={gamma:.6f})")
