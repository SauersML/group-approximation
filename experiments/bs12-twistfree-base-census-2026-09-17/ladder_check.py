"""Numerical check of the dyadic scale-ladder gauge identity.

h = exp(i Y_K(V)),  Y_K(V) = -s sum_{k<K} (V^(2^k) + V^(-2^k)).
Claim:  h^* A_s h = W exp(i s H_R) exactly, R = 2^K, H_R = V^R + V^(-R),
        ||h^* D h - D|| <= 4 pi s (R - 1) / N,
and sigma_R^* W exp(i s H_R) sigma_R = A_s, sigma_R^* D sigma_R = D^R
(sigma_R e_j = e_(R j mod N)).

usage: python3 ladder_check.py
"""
import math, numpy as np
from scipy.linalg import expm


def ops(N):
    j = np.arange(N)
    D = np.diag(np.exp(2j * math.pi * j / N))
    W = np.zeros((N, N), complex); W[(j * ((N + 1) // 2)) % N, j] = 1
    V = np.zeros((N, N), complex); V[(j + 1) % N, j] = 1
    return D, W, V


def main():
    for N in (27, 81, 243):
        D, W, V = ops(N)
        Vp = lambda n: np.linalg.matrix_power(V, n % N)
        for s in (0.1, 0.5):
            A = W @ expm(1j * s * (V + V.conj().T))
            for K in (1, 2, 3, 4):
                R = 2 ** K
                Y = -s * sum(Vp(2 ** k) + Vp(-(2 ** k)) for k in range(K))
                h = expm(1j * Y)
                lhs = h.conj().T @ A @ h
                rhs = W @ expm(1j * s * (Vp(R) + Vp(-R)))
                e1 = np.linalg.norm(lhs - rhs, 2)
                e2 = np.linalg.norm(h.conj().T @ D @ h - D, 2)
                bnd = 4 * math.pi * s * (R - 1) / N
                j = np.arange(N)
                S = np.zeros((N, N), complex); S[(R * j) % N, j] = 1
                e3 = np.linalg.norm(S.conj().T @ rhs @ S - A, 2)
                e4 = np.linalg.norm(S.conj().T @ D @ S - np.linalg.matrix_power(D, R), 2)
                print(f"N={N} s={s} R={R}: |h*Ah - W e^(isH_R)|={e1:.1e} "
                      f"||h*Dh-D||={e2:.4f} <= {bnd:.4f} {e2 <= bnd + 1e-12}  "
                      f"sigma checks {e3:.1e} {e4:.1e}")


if __name__ == "__main__":
    main()
