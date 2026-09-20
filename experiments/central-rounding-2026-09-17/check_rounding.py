#!/usr/bin/env python3
"""Sanity check for the rounding step of
central-power-quotient-gaps-converge-to-the-extension-gap-proof (Step 2).

For random unitaries U_a, U_b, U_z and relators taken from the torus-knot
presentation of T-bar (a^4 = z, b^3 = z, (ba)^5 = z^3, [z,a], [z,b]), we round U_z
to the nearest m-th roots of unity and check that
  (1) (U'_z)^m = 1,
  (2) ||U'_z - U_z|| <= pi/m,
  (3) def_R(U') <= def_R(U) + L*pi/m, where L = max number of z-letters (here 3),
  (4) ||U'_z - 1|| >= ||U_z - 1|| - pi/m.
Only the rounding inequality is tested; nothing here is a group-theoretic claim.
Run: python3 check_rounding.py  (prints OK and the worst slack)
"""
import numpy as np

rng = np.random.default_rng(20260919)


def haar(k):
    x = (rng.normal(size=(k, k)) + 1j * rng.normal(size=(k, k))) / np.sqrt(2)
    q, r = np.linalg.qr(x)
    return q * (np.diag(r) / abs(np.diag(r)))


def near(u, eps):
    """A unitary within about eps of u (perturbation by exp(i eps H))."""
    k = u.shape[0]
    h = rng.normal(size=(k, k)) + 1j * rng.normal(size=(k, k))
    h = (h + h.conj().T) / 2
    h /= np.linalg.norm(h, 2)
    w, v = np.linalg.eigh(h)
    return v @ np.diag(np.exp(1j * eps * w)) @ v.conj().T @ u


def round_m(u, m):
    # u is normal, so its complex Schur form is diagonal with unitary basis z
    from scipy.linalg import schur
    t, z = schur(u, output="complex")
    d = np.diag(t)
    th = np.angle(d)
    j = np.round(th * m / (2 * np.pi))
    return z @ np.diag(np.exp(2j * np.pi * j / m)) @ z.conj().T


def n2(x):
    return np.linalg.norm(x, 2)


def mp(u, p):
    return np.linalg.matrix_power(u, p)


def relators(a, b, zz):
    i = np.eye(a.shape[0])
    zi = zz.conj().T
    return [
        mp(a, 4) @ zi,
        mp(b, 3) @ zi,
        mp(b @ a, 5) @ zi @ zi @ zi,
        zz @ a @ zi @ a.conj().T,
        zz @ b @ zi @ b.conj().T,
    ], i


L = 3
worst = np.inf
for trial in range(300):
    k = int(rng.integers(2, 9))
    m = int(rng.choice([2, 3, 4, 8, 16, 32, 64]))
    a = haar(k)
    b = haar(k)
    zz = near(mp(a, 4), float(rng.uniform(0, 0.5)))
    rels, i = relators(a, b, zz)
    d0 = max(n2(r - i) for r in rels)
    z2 = round_m(zz, m)
    rels2, _ = relators(a, b, z2)
    d1 = max(n2(r - i) for r in rels2)
    assert n2(mp(z2, m) - i) < 1e-8, "not an m-th root"
    assert n2(z2 - zz) <= np.pi / m + 1e-9, "rounding too far"
    assert d1 <= d0 + L * np.pi / m + 1e-9, "defect bound fails"
    assert n2(z2 - i) >= n2(zz - i) - np.pi / m - 1e-9, "displacement bound fails"
    worst = min(worst, d0 + L * np.pi / m - d1)
print("OK: 300 trials; minimal slack in defect bound =", round(float(worst), 6))
