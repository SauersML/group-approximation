"""Shift-covariant local models of Thompson's group F in the qubit Bernoulli algebra.

Ansatz: x_0 = a, x_1 = sigma(a), with a a unitary on sites [0, L) of the one-sided
qubit chain and sigma the tensor shift.  The relations of F reduce to

    (A)  a* sigma(a) a  = sigma^2(a)
    (B)  a* sigma^2(a) a = sigma^3(a)

(all other relations are sigma-images of these).  We minimise the normalised
Hilbert-Schmidt defect of (A) and (B) over a = expm(iH), H Hermitian on L qubits,
subject to the non-commutation constraint ||[a, sigma a]||_2 >= c, enforced by a
quadratic penalty.  Everything lives on N = L + 3 sites.

Output: for each (L, c) the best defect found over several random restarts, next to the
proved lower bound c / (5^(L-1) - 1) for the (A)-defect alone
(thompson-f-exact-shift-covariant-models-force-amenability, item 4).
Usage:  python3 search.py [Lmax] [restarts]
"""
import os
import sys

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize

rng = np.random.default_rng(20260917)


def shifted(a, L, k, N):
    """sigma^k(a) as a 2^N x 2^N matrix: I_{2^k} (x) a (x) I_{2^(N-L-k)}."""
    return np.kron(np.kron(np.eye(2 ** k), a), np.eye(2 ** (N - L - k)))


def hs(x):
    """Normalised Hilbert-Schmidt norm ||x||_2 = sqrt(tr(x*x)/dim)."""
    return np.sqrt(np.real(np.vdot(x, x)) / x.shape[0])


def herm(p, n):
    m = np.zeros((n, n), dtype=complex)
    iu = np.triu_indices(n, 1)
    k = len(iu[0])
    m[iu] = p[:k] + 1j * p[k:2 * k]
    m = m + m.conj().T
    m[np.diag_indices(n)] = p[2 * k:]
    return m


def defects(a, L):
    N = L + 3
    s = [shifted(a, L, k, N) for k in range(4)]
    A = s[0].conj().T @ s[1] @ s[0] - s[2]
    B = s[0].conj().T @ s[2] @ s[0] - s[3]
    C = s[0] @ s[1] - s[1] @ s[0]
    return hs(A), hs(B), hs(C)


def objective(p, L, c, mu):
    n = 2 ** L
    a = expm(1j * herm(p, n))
    dA, dB, dC = defects(a, L)
    return dA ** 2 + dB ** 2 + mu * max(0.0, c - dC) ** 2


def run(L, c, restarts, mu=1.0e4):
    n = 2 ** L
    best = None
    for _ in range(restarts):
        p0 = rng.normal(scale=1.0, size=n * n)
        res = minimize(objective, p0, args=(L, c, mu), method="L-BFGS-B",
                       options={"maxiter": 300})
        a = expm(1j * herm(res.x, n))
        dA, dB, dC = defects(a, L)
        rec = (float(np.hypot(dA, dB)), float(dC))
        if dC >= 0.98 * c and (best is None or rec[0] < best[0]):
            best = rec
    return best


if __name__ == "__main__":
    Lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    print("L  c     min_defect(A,B)  achieved_commutator  proved_lower_bound")
    for L in range(2, Lmax + 1):  # L = 1: a and sigma(a) sit on disjoint sites and commute
        for c in (0.1, 0.3, 0.6):
            best = run(L, c, restarts)
            if best is None:
                print(f"{L}  {c:.1f}   (constraint not met)")
            else:
                print(f"{L}  {c:.1f}   {best[0]:.4f}           {best[1]:.4f}               {c / (5 ** (L - 1) - 1):.4f}")
        sys.stdout.flush()
