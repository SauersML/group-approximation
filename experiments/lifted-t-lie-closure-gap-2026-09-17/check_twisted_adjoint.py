"""Sanity checks for lifted-thompson-t-twisted-witnesses-need-unbounded-lie-closure.

K = K(3,4) = <x, y | x^4 = y^3>, c = x^4.  Relators of T-bar over K:
  rho1 = [yxy, x^2 yxy x^2],  rho2 = [yxy, x^2 y^2 x^2 yxy x^2 y x^2],  rhoP = (yx)^5 x^-12.
Words are read as matrix products left to right.

1. Twisted character line: x -> t^3, y -> t^4.  Exactly rhoP -> t^-1 and c -> t^12, so
   |sigma(c) - 1| / D -> 12 as t -> 1.
2. Adjoint transfer on random exact K-representations (A^4 = B^3 = mu*1, scalar mu):
   Ad(A)^4 = 1 exactly, Ad kills c, and D_T(Ad o sigma) <= 2 D_Tbar(sigma).
3. Fixed-group amplification: Sym^m of 2-dimensional SU(2) representations of K
   (A^4 = B^3 = -1).  All have Lie closure SU(2) or SO(3) (N = 3), so the theorem
   predicts min D >= min(1/2, delta_3/2).  Observed: m = 1 gives 2 sin(pi/24) = 0.2611,
   m = 2 (an exact SO(3) representation of G0, hence of T) gives 2 sin(pi/12) = 0.5176,
   so delta_3 <= 2 sin(pi/12) and the factor 2 of the adjoint transfer is nearly attained
   (0.5176 / 0.2611 = 1.98).  For m >= 2 the minimum stays >= 1/2 and grows with m.
"""
import json
import numpy as np

rng = np.random.default_rng(20260920)


def comm(g, h):
    return g @ h @ np.linalg.inv(g) @ np.linalg.inv(h)


def word(s, A, B):
    n = A.shape[0]
    M = np.eye(n, dtype=complex)
    for ch in s:
        M = M @ (A if ch == "x" else B)
    return M


def relator_images(A, B):
    X = word("yxy", A, B)
    J = word("xx", A, B)
    W = word("xxyyxx", A, B)
    r1 = comm(X, J @ X @ J)
    r2 = comm(X, W @ X @ np.linalg.inv(W))
    rP = np.linalg.matrix_power(B @ A, 5) @ np.linalg.matrix_power(np.linalg.inv(A), 12)
    return r1, r2, rP


def opn(M):
    return float(np.linalg.norm(M, 2))


def defect(A, B):
    n = A.shape[0]
    return max(opn(r - np.eye(n)) for r in relator_images(A, B))


def haar(n):
    Z = (rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))) / np.sqrt(2)
    Q, R = np.linalg.qr(Z)
    return Q @ np.diag(np.diag(R) / abs(np.diag(R)))


def ad(U):
    # Ad(U) on M_n(C) (Hilbert-Schmidt), as the matrix U (x) conj(U) acting on vec(X).
    return np.kron(U, U.conj())


out = {}

# 1. twisted characters
line = []
for th in [1e-1, 1e-2, 1e-3, 1e-4]:
    t = np.exp(1j * th)
    A = np.array([[t ** 3]]); B = np.array([[t ** 4]])
    r1, r2, rP = relator_images(A, B)
    D = defect(A, B)
    zc = abs(t ** 12 - 1)
    line.append({"theta": th, "rhoP_times_t": complex(rP[0, 0] * t).real,
                 "r1": abs(r1[0, 0] - 1), "r2": abs(r2[0, 0] - 1), "D": D,
                 "ratio_zmove_over_D": zc / D})
out["twisted_character_line"] = line

# 2. adjoint transfer on random exact scalar-twisted K-representations
worst = 0.0
records = []
for trial in range(200):
    n = int(rng.integers(2, 6))
    theta = rng.uniform(0, 1)
    mu = np.exp(2j * np.pi * theta)
    a4 = mu ** 0.25 * 1j ** rng.integers(0, 4, n)
    b3 = mu ** (1 / 3) * np.exp(2j * np.pi * rng.integers(0, 3, n) / 3)
    U, V = haar(n), haar(n)
    A = U @ np.diag(a4) @ U.conj().T
    B = V @ np.diag(b3) @ V.conj().T
    assert np.allclose(np.linalg.matrix_power(A, 4), mu * np.eye(n))
    assert np.allclose(np.linalg.matrix_power(B, 3), mu * np.eye(n))
    D = defect(A, B)
    Ad_A, Ad_B = ad(A), ad(B)
    assert np.allclose(np.linalg.matrix_power(Ad_A, 4), np.eye(n * n))
    assert np.allclose(np.linalg.matrix_power(Ad_B, 3), np.eye(n * n))
    # T-relators of the G0-representation Ad o sigma
    X = Ad_B @ Ad_A @ Ad_B
    J = Ad_A @ Ad_A
    W = Ad_A @ Ad_A @ Ad_B @ Ad_B @ Ad_A @ Ad_A
    I = np.eye(n * n)
    DT = max(opn(comm(X, J @ X @ J) - I), opn(comm(X, W @ X @ np.linalg.inv(W)) - I),
             opn(np.linalg.matrix_power(Ad_B @ Ad_A, 5) - I))
    worst = max(worst, DT / (2 * D))
    records.append((n, D, DT))
out["adjoint_transfer"] = {"trials": len(records), "max_DT_over_2D": worst}

# 3. Sym^m amplification of SU(2) representations with A^4 = B^3 = -1


def su2(axis, ang):
    axis = axis / np.linalg.norm(axis)
    sx = np.array([[0, 1], [1, 0]], complex); sy = np.array([[0, -1j], [1j, 0]]); sz = np.diag([1, -1]).astype(complex)
    Hm = axis[0] * sx + axis[1] * sy + axis[2] * sz
    return np.cos(ang / 2) * np.eye(2) - 1j * np.sin(ang / 2) * Hm


def sym_power(g, m):
    # action on homogeneous polynomials of degree m in two variables, basis u^(m-k) v^k
    from math import comb
    a, b = g[0, 0], g[0, 1]
    cc, d = g[1, 0], g[1, 1]
    M = np.zeros((m + 1, m + 1), complex)
    # g acts by u -> a u + c v, v -> b u + d v
    for k in range(m + 1):
        # expand (a u + c v)^(m-k) (b u + d v)^k
        p1 = np.zeros(m + 1, complex)
        for i in range(m - k + 1):
            p1[i] += comb(m - k, i) * a ** (m - k - i) * cc ** i
        p2 = np.zeros(m + 1, complex)
        for j in range(k + 1):
            p2[j] += comb(k, j) * b ** (k - j) * d ** j
        prod = np.convolve(p1, p2)[: m + 1]
        M[:, k] = prod
    # make unitary in the orthonormal basis sqrt(comb) scaling
    s = np.array([np.sqrt(comb(m, k)) for k in range(m + 1)])
    return np.diag(1 / s) @ M @ np.diag(s)


A2 = su2(np.array([0.0, 0.0, 1.0]), np.pi / 2)      # rotation angle pi/2, A2^4 = -1
sym = []
for m in range(1, 25):
    best = 9.0
    for phi in np.linspace(0.0, np.pi, 181):
        B2 = su2(np.array([np.sin(phi), 0.0, np.cos(phi)]), 2 * np.pi / 3)  # B2^3 = -1
        Am, Bm = sym_power(A2, m), sym_power(B2, m)
        best = min(best, defect(Am, Bm))
    sym.append({"m": m, "min_D_over_axis_angle": best})
out["sym_power_su2"] = sym
out["sym_power_min_over_m"] = min(r["min_D_over_axis_angle"] for r in sym)
out["sym_power_min_over_m_ge_2"] = min(r["min_D_over_axis_angle"] for r in sym if r["m"] >= 2)
out["reference_2sin_pi_over_24"] = 2 * np.sin(np.pi / 24)
out["reference_2sin_pi_over_12"] = 2 * np.sin(np.pi / 12)

print(json.dumps(out, indent=1))
