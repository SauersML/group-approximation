"""Referee check of the individual proof steps (lane ref-04, 2026-09-17).

For random Pauli sums (distinct non-identity Paulis, n = 1..4) this checks, at the
first post-selection step of the route's proof:
  (F1)  x_R^2 + x_Q^2 <= 1 for every Q anticommuting with R
  (1)   a <= (sqrt2-1)(1+M) W_A
  (2)   <psi_1|K|psi_1> = lambda - a/(1+M)
  (3)   Pi K Pi restricted to range(Pi) equals w_R + (Pi K_C Pi restricted), and
        lambda_max of that compression >= lambda - a/(1+M)
  (4)   the (n-1)-qubit sum K' built symbolically (conjugating A_R to Z_n by a
        Clifford found by search is avoided: instead we check that the compression of
        K_C to range(Pi) is a sum of operators Pi A_Q Pi, each unitarily a signed
        (n-1)-qubit Pauli, so its weight is <= sum_C w_Q), via the Hilbert-Schmidt
        test tr((Pi A_Q Pi)^2) = tr(Pi) and that Pi A_Q Pi != +-Pi.
Also scans F2 on a fine grid.
usage: python3 referee_ref04_steps.py trials seed
"""
import itertools
import sys
import numpy as np

t = np.sqrt(2) - 1
Ms = np.linspace(0, 1, 2000001)
gap = t * (1 + Ms) - np.minimum(Ms, np.sqrt(1 - Ms ** 2))
print("F2 grid min of t(1+M)-min{M,sqrt(1-M^2)}:", gap.min(), "at M =", Ms[gap.argmin()])

S1 = [np.eye(2), np.array([[0, 1], [1, 0]]), np.array([[0, -1j], [1j, 0]]), np.diag([1, -1])]


def pauli(lab):
    out = np.array([[1]], dtype=complex)
    for i in lab:
        out = np.kron(out, S1[i])
    return out


trials = int(sys.argv[1])
rng = np.random.default_rng(int(sys.argv[2]))
worst = {"F1": -9, "(1)": -9, "(2)": 0, "(3)": 0, "(3b)": -9, "(4)": 0}
for tr in range(trials):
    n = int(rng.integers(1, 5))
    labs = list(itertools.product(range(4), repeat=n))[1:]
    k = int(rng.integers(1, min(len(labs), 9) + 1))
    idx = rng.choice(len(labs), k, replace=False)
    w = np.abs(rng.standard_normal(k)) + 1e-3
    s = rng.choice([-1, 1], k)
    A = [s[j] * pauli(labs[i]) for j, i in enumerate(idx)]
    K = sum(wj * Aj for wj, Aj in zip(w, A))
    ev, V = np.linalg.eigh(K)
    lam, psi = ev[-1], V[:, -1]
    x = np.array([np.vdot(psi, Aj @ psi).real for Aj in A])
    r = int(np.argmax(x))
    M = x[r]
    AR = A[r]
    anti = [j for j in range(k) if j != r and np.allclose(AR @ A[j], -A[j] @ AR)]
    comm = [j for j in range(k) if j != r and j not in anti]
    WA = w[anti].sum()
    a = sum(w[j] * x[j] for j in anti)
    for j in anti:
        worst["F1"] = max(worst["F1"], M ** 2 + x[j] ** 2 - 1)
    worst["(1)"] = max(worst["(1)"], a - t * (1 + M) * WA)
    Pi = (np.eye(2 ** n) + AR) / 2
    p1 = Pi @ psi
    p1 /= np.linalg.norm(p1)
    e1 = np.vdot(p1, K @ p1).real
    worst["(2)"] = max(worst["(2)"], abs(e1 - (lam - a / (1 + M))))
    ew, EV = np.linalg.eigh(Pi)
    B = EV[:, ew > 0.5]  # orthonormal basis of range(Pi)
    KC = sum((w[j] * A[j] for j in comm), np.zeros_like(K))
    comp = B.conj().T @ K @ B
    compC = B.conj().T @ KC @ B
    worst["(3)"] = max(worst["(3)"], np.abs(comp - (w[r] * np.eye(B.shape[1]) + compC)).max())
    lp = np.linalg.eigvalsh(compC)[-1] if B.shape[1] else 0
    worst["(3b)"] = max(worst["(3b)"], (lam - a / (1 + M) - w[r]) - lp)
    for j in comm:
        Q = B.conj().T @ A[j] @ B
        d = B.shape[1]
        bad = (not np.allclose(Q @ Q, np.eye(d))) or np.allclose(Q, np.eye(d)) or np.allclose(Q, -np.eye(d)) \
            or (d > 1 and abs(np.trace(Q)) > 1e-9)
        worst["(4)"] = max(worst["(4)"], int(bad))
print("worst excess over each claimed inequality (<= ~1e-12 means no violation):")
for kk, vv in worst.items():
    print(f"  {kk}: {vv:.3e}")
