#!/usr/bin/env python3
"""Verify the row-wise trivial-gauge floor (OGT1)-(OGT3).

For one selector row (r,q), a reflection C_q=1-2F_q with tau(F_q)=q, an
involution D on the reservoir, T=C_q tensor D, a source reflection
R=1-2E with tau(E)=r and any unitary W:

    |r-q| <= (1/2)||W R W^*-T||_2 + |2q-1| ||1-D||_2^2/4.      (OGT1)

Rows: (1/2,1/4) gives delta_1 + ||1-D_1||^2/4 >= 1/2          (OGT2)
      (1/4,1/8) gives delta_2 + (3/8)||1-D_2||^2 >= 1/4       (OGT3)
with delta=||WRW^*-T||_2 (normalized trace).  The script checks:
  1. the identity 1-theta(D)=||1-D||_2^2/4;
  2. (OGT1) on random unitaries W and random involutions D;
  3. exact tightness on the OAP gauges (theta=1/2 and theta=5/6,
     exactly conjugate rows, delta=0);
  4. D=1 is never compatible with an exact row: Phi_q(1)=q != r.
"""
from fractions import Fraction as Fr
import numpy as np

rng = np.random.default_rng(20260917)


def ntr(x):
    return np.trace(x).real / x.shape[0]


def hs(x):
    return np.sqrt(max(ntr(x.conj().T @ x), 0.0))


def refl(n, k):
    d = np.ones(n)
    d[:k] = -1
    return np.diag(d)


def haar(n):
    z = (rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / abs(np.diag(r)))


def rand_inv(m):
    k = int(rng.integers(0, m + 1))
    u = haar(m)
    return u @ refl(m, k) @ u.conj().T


def phi(q, th):
    return 1 - q + (2 * q - 1) * th


# 1. theta identity and 2. random test of (OGT1)
worst = 1.0
for trial in range(400):
    q, r, n = [(Fr(1, 4), Fr(1, 2), 4), (Fr(1, 8), Fr(1, 4), 8)][trial % 2]
    m = int(rng.integers(1, 7))
    D = rand_inv(m)
    th = ntr((np.eye(m) + D) / 2)
    assert abs((1 - th) - hs(np.eye(m) - D) ** 2 / 4) < 1e-10
    T = np.kron(refl(n, int(q * n)), D)
    N = n * m
    R = refl(N, int(r * N))
    W = haar(N) if trial % 3 else np.eye(N)
    delta = hs(W @ R @ W.conj().T - T)
    lhs = float(abs(r - q))
    rhs = delta / 2 + abs(2 * float(q) - 1) * hs(np.eye(m) - D) ** 2 / 4
    assert lhs <= rhs + 1e-10, (trial, lhs, rhs)
    worst = min(worst, rhs - lhs)
print("random (OGT1) checks passed; min slack", round(worst, 6))

# 3. tightness on the OAP gauges: exact rows, delta=0, equality in (OGT2),(OGT3)
for (r, q, th, name) in [(Fr(1, 2), Fr(1, 4), Fr(1, 2), "row 1"),
                         (Fr(1, 4), Fr(1, 8), Fr(5, 6), "row 2")]:
    assert phi(q, th) == r
    gap2 = 4 * (1 - th)  # ||1-D||_2^2
    c = abs(2 * q - 1) / 2  # coefficient after multiplying (OGT1) by 2
    lhs = 0 + 2 * c * gap2 / 2
    assert lhs == 2 * abs(r - q), (name, lhs)
    print(name, "theta", th, "||1-D||^2", gap2, "floor attained exactly")

# numerical realisation: OAP dimensions 28 (theta 1/2) and 48 (theta 5/6)
for (n, q, m, th, r) in [(4, Fr(1, 4), 28, Fr(1, 2), Fr(1, 2)),
                         (8, Fr(1, 8), 48, Fr(5, 6), Fr(1, 4))]:
    D = refl(m, int((1 - th) * m))
    T = np.kron(refl(n, int(q * n)), D)
    negT = int(round(ntr((np.eye(n * m) - T) / 2) * n * m))
    assert Fr(negT, n * m) == r
    # R and T are conjugate by a permutation, so delta=0 is attained
    print("OAP dim", n * m, "negative fraction of T", Fr(negT, n * m), "= r")

# 4. trivial gauge is incompatible with an exact row
for (r, q) in [(Fr(1, 2), Fr(1, 4)), (Fr(1, 4), Fr(1, 8))]:
    assert phi(q, Fr(1)) == q != r
    print("row", (r, q), ": D=1 forces negative fraction", q, "!=", r,
          "; floor delta >=", 2 * abs(r - q))
print("ALL CHECKS PASSED")
