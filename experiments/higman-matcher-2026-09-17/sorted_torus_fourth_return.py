"""Numerical scout of the sorted primitive-shell fourth return (SPT7).

Objects (primitive-shell-sorted-matcher-is-one-phase-torus):
  q=3^n, L=2q/3, e_a=e_(2^a mod q), P e_a=e_(a-1), omega=exp(2 pi i/L),
  f(a)=floor(2u_a/3), B=diag(omega^f(a)), H_(a,b)=L^(-1/2) omega^(-f(a) b),
  so H P H^* = B, and every sorted matcher is K=RH with R diagonal.
Quantity: r(R)=||K^4 P - P K^4||, both operator norm and normalized HS.

Mode "torus": local minimization of the normalized-HS return over R
  (random starts, analytic gradient, L-BFGS-B).
Mode "general": Riemannian descent over all unitaries K of
  lam*||KP-DK||_2^2/L + ||K^4P-PK^4||_2^2/L  (D the exact clock, PDP^*=D^2).

Local optimization only: every number below is an UPPER bound on the
infimum over the stated class, never a lower bound.

Recorded runs (2026-09-17, seeds 0/1/7):
  torus, HS-min found:  n=2 (L=6)  0.766  [30 starts]
                        n=3 (L=18) 0.579  [46 starts + chirp grid; op 0.881]
                        n=4 (L=54) 1.271  [14 starts + chirp grid; op ~2.0]
  general lam=1:  n=2 eps op/hs 0.89/0.57 ret op/hs 0.059/0.036
                  n=3 eps 0.61/0.30  ret 0.071/0.042
                  n=4 eps 0.52/0.25  ret 0.071/0.036
  general lam=30: n=3 eps 0.28/0.19  ret 0.47/0.30
                  n=4 eps 0.32/0.15  ret 1.23/0.61
Usage: python3 sorted_torus_fourth_return.py torus N STARTS
       python3 sorted_torus_fourth_return.py general N STARTS LAM
"""
import sys
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize


def setup(n):
    q = 3**n
    L = 2*q//3
    u = np.array([pow(2, a, q) for a in range(L)])
    f = (2*u)//3
    w = np.exp(2j*np.pi/L)
    P = np.zeros((L, L))
    for a in range(L):
        P[(a-1) % L, a] = 1
    H = w**(-np.outer(f, np.arange(L))) / np.sqrt(L)
    D = np.diag(np.exp(2j*np.pi*u/q))
    assert np.allclose(H @ P @ H.conj().T, np.diag(w**f))
    assert np.allclose(P @ D @ P.T, D @ D)
    return L, P, H, D


def opn(M):
    return np.linalg.norm(M, 2)


def torus_obj(th, P, H):
    L = len(th)
    K = np.exp(1j*th)[:, None]*H
    Ks = [np.eye(L, dtype=complex)]
    for _ in range(4):
        Ks.append(Ks[-1] @ K)
    C = Ks[4] @ P - P @ Ks[4]
    val = np.real(np.vdot(C, C))
    M = P @ C.conj().T - C.conj().T @ P
    g = 2*sum(np.real(1j*np.diag(Ks[4-m] @ M @ Ks[m])) for m in range(4))
    F = np.sqrt(val/L)
    return F, g/(2*L*F)


def general_fg(K, P, D, lam):
    L = K.shape[0]
    C1 = K @ P - D @ K
    K2 = K @ K
    X = K2 @ K2
    C = X @ P - P @ X
    f = lam*np.real(np.vdot(C1, C1)) + np.real(np.vdot(C, C))
    G1 = C1 @ P.T - D.conj().T @ C1
    MX = C @ P.T - P.T @ C
    Ks = [np.eye(L, dtype=complex), K, K2, K2 @ K]
    G2 = sum(Ks[m].conj().T @ MX @ Ks[3-m].conj().T for m in range(4))
    return f/L, (lam*G1 + G2)/L


def general_descend(K, P, D, lam, iters=3000):
    f, G = general_fg(K, P, D, lam)
    eta = 1.0
    for _ in range(iters):
        Om = K.conj().T @ G
        Om = Om - Om.conj().T
        while True:
            Kn = K @ expm(-eta*Om)
            fn, Gn = general_fg(Kn, P, D, lam)
            if fn < f or eta < 1e-8:
                break
            eta /= 2
        if f - fn < 1e-13:
            break
        K, f, G = Kn, fn, Gn
        eta *= 1.5
    return K


def report(tag, K, P, D, L):
    X = np.linalg.matrix_power(K, 4)
    C = X @ P - P @ X
    E = K @ P @ K.conj().T - D
    print(tag, "eps op/hs", round(opn(E), 4), round(np.linalg.norm(E)/np.sqrt(L), 4),
          "ret op/hs", round(opn(C), 4), round(np.linalg.norm(C)/np.sqrt(L), 4), flush=True)


if __name__ == "__main__":
    mode, n, starts = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    L, P, H, D = setup(n)
    rng = np.random.default_rng(7)
    for t in range(starts):
        if mode == "torus":
            th = rng.uniform(0, 2*np.pi, L)
            th = minimize(torus_obj, th, args=(P, H), jac=True, method="L-BFGS-B",
                          options={"maxiter": 3000}).x
            K = np.exp(1j*th)[:, None]*H
        else:
            lam = float(sys.argv[4])
            Z = rng.normal(size=(L, L)) + 1j*rng.normal(size=(L, L))
            K = general_descend(np.linalg.qr(Z)[0], P, D, lam)
        report(f"{mode} n={n} start={t}", K, P, D, L)
