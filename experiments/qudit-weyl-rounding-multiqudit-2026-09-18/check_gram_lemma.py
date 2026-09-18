"""Check the commutator-Gram uncertainty inequality
   sum_i w_i delta_i >= ||D C D||_1 / 4,  C_ij = (1 - omega^{t_ij}) <u_i^* u_j>,
and its Frobenius corollary, on random states and random Weyl operators (n qudits),
including states near the top eigenvector of a random Weyl sum (the tight regime).
Also prints the one-qudit constant c*(d) solving c(c-3)/(c+1) = 2/(sqrt3 sin(pi/d))."""
import numpy as np
rng = np.random.default_rng(0)
def weyl(d, n, v):
    w = np.exp(2j*np.pi/d); X = np.roll(np.eye(d), 1, 0); Z = np.diag(w**np.arange(d))
    M = np.eye(1)
    for k in range(n):
        M = np.kron(M, np.linalg.matrix_power(X, v[k]) @ np.linalg.matrix_power(Z, v[n+k]))
    return M
def symp(d, n, a, b): return int(sum(a[n+k]*b[k] - a[k]*b[n+k] for k in range(n))) % d
worst = 9; worstF = 9
for trial in range(3000):
    d = int(rng.choice([3, 5, 7])); n = 1 if d == 7 else int(rng.integers(1, 3)); k = int(rng.integers(2, 6))
    vs = [rng.integers(0, d, 2*n) for _ in range(k)]
    if any(not v.any() for v in vs): continue
    us = [np.exp(2j*np.pi*rng.random()) * weyl(d, n, v) for v in vs]
    if trial % 2:
        psi = rng.standard_normal(d**n) + 1j*rng.standard_normal(d**n)
    else:  # top eigenvector of Hermitian sum of the u's: small delta regime
        K = sum(u + u.conj().T for u in us); psi = np.linalg.eigh(K)[1][:, -1]
    psi /= np.linalg.norm(psi)
    w = rng.random(k)
    delta = np.array([1 - np.real(psi.conj() @ u @ psi) for u in us])
    om = np.exp(2j*np.pi/d)
    t = np.array([[symp(d, n, vs[i], vs[j]) for j in range(k)] for i in range(k)])
    # u_i u_j = omega^{t_ij} u_j u_i: determine t numerically to avoid convention errors
    tt = np.zeros((k, k), int)
    for i in range(k):
        for j in range(k):
            A = us[i] @ us[j]; B = us[j] @ us[i]
            ph = np.vdot(B.flatten(), A.flatten()) / np.vdot(B.flatten(), B.flatten())
            tt[i, j] = int(round(np.angle(ph) / (2*np.pi/d))) % d
    C = np.array([[(1 - om**tt[i, j]) * (psi.conj() @ us[i].conj().T @ us[j] @ psi) for j in range(k)] for i in range(k)])
    D = np.sqrt(w)
    lhs = (w*delta).sum(); rhs = np.abs(np.linalg.eigvalsh(D[:, None]*C*D[None, :])).sum()/4
    worst = min(worst, lhs - rhs)
    z = np.array([[psi.conj() @ us[i].conj().T @ us[j] @ psi for j in range(k)] for i in range(k)])
    fro = np.sqrt(sum(w[i]*w[j]*np.sin(np.pi*tt[i, j]/d)**2*abs(z[i, j])**2 for i in range(k) for j in range(i+1, k)))
    worstF = min(worstF, lhs - fro)
print("min over trials of  sum w delta - ||DCD||_1/4           =", worst)
print("min over trials of  sum w delta - Frobenius lower bound  =", worstF)
for d in [5, 7, 11, 13, 31, 101, 1009]:
    A = 2/(np.sqrt(3)*np.sin(np.pi/d)); c = ((3+A) + np.sqrt((3+A)**2 + 4*A))/2
    print(f"d={d}: c*(d) = {c:.4f}   2d/(sqrt3 pi) = {2*d/(np.sqrt(3)*np.pi):.4f}   difference = {c - 2*d/(np.sqrt(3)*np.pi):.4f}")
