"""Checks for bs12-separated-doubling-spectrum-conjugators-correct-without-padding.

1. Wiener norm of the truncated Cauchy kernel psi_gamma (proof, Step 2):
   ||psi||_A <= 1/2 + 2.33/gamma for gamma <= 1.
2. The pinching/polar correction on the Fourier-twisted pair
   A_s = W exp(is(V+V*)), B' = D (spectrum = N-th roots of unity, N odd):
   exact C with C D C* = D^2 and ||C - A|| <= 2 M eta, and the dimension-free
   lower bound ||C - A|| >= |J_1(2s)|/2 - tail for every exact C fixing D.
"""
import numpy as np
from scipy.special import jv


def wiener_norm(gamma, M=1 << 20):
    th0 = 2 * np.arcsin(gamma / 2)
    th = 2 * np.pi * np.arange(M) / M
    th = np.where(th > np.pi, th - 2 * np.pi, th)
    c = 1 / np.tan(th0 / 2)
    with np.errstate(divide="ignore", invalid="ignore"):
        kap = np.where(np.abs(th) >= th0, 1 / np.tan(th / 2), c * th / th0)
    psi = -0.5 - 0.5j * kap
    return np.abs(np.fft.fft(psi) / M).sum()


def pair(N, s):
    h = pow(2, -1, N)
    j = np.arange(N)
    D = np.diag(np.exp(2j * np.pi * j / N))
    V = np.roll(np.eye(N), 1, axis=0)
    W = np.zeros((N, N))
    W[(h * j) % N, j] = 1.0
    ev, U = np.linalg.eigh(V + V.T)
    return W @ U @ np.diag(np.exp(1j * s * ev)) @ U.conj().T, D, W


def correct(A, D):
    """A' = sum_y Q_y A P_y with Q_y = spectral projection of D^2 at y."""
    N = D.shape[0]
    d = np.diag(D)
    d2 = d * d
    Ap = np.zeros_like(A)
    for i in range(N):  # D^2 eigenvector e_i has eigenvalue d2[i] = d[k]
        k = np.argmin(np.abs(d - d2[i]))
        Ap[i, k] = A[i, k]
    u, sv, vh = np.linalg.svd(Ap)
    return u @ vh, np.linalg.norm(Ap - A, 2)


if __name__ == "__main__":
    print("gamma  gamma*||psi||_A  bound gamma/2+2.33")
    for g in (1.0, 0.5, 0.1, 0.03, 0.01, 0.003):
        w = wiener_norm(g)
        print(f"{g:6.3f}  {g*w:8.4f}  {g/2+2.33:8.4f}  ok={w <= 0.5+2.33/g}")
    for s in (0.05, 0.1, 0.25):
        for N in (45, 135):
            A, D, W = pair(N, s)
            gam = abs(np.exp(2j * np.pi / N) - 1)
            eta = np.linalg.norm(A @ D @ A.conj().T - D @ D, 2)
            C, off = correct(A, D)
            exact = np.linalg.norm(C @ D @ C.conj().T - D @ D, 2)
            dist = np.linalg.norm(C - A, 2)
            Mg = 1 + 2.33 / min(gam, 1)
            lower = abs(jv(1, 2 * s)) / 2 - sum(abs(jv(m, 2 * s)) for m in range(N - 1, N + 3))
            print(f"s={s} N={N} eta/gamma={eta/gam:.3f} exact={exact:.1e} "
                  f"||C-A||={dist:.4f} upper 2M eta={2*Mg*eta:.4f} lower={lower:.4f}")
