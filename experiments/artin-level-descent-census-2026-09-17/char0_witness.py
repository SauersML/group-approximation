"""Characteristic-0 version of the non-descending 2-dim witness for the opposite-twos joins
(2, q, 2, p): halves ac = 2, bc = q, be = 2, ae = p, chi = (1, 1, -1, -1).

Ansatz: ac = [[-1, x], [0, 1]], be = [[-1, y], [0, 1]] (reflections sharing the (-1)-eigenvector e1),
b = beta I + gamma a (commutes with a), c = a^-1 ac, e = b^-1 be, and require
  [c, e] = 0,  bc with eigenvalues zeta_q^i, zeta_q^-i,  ae with eigenvalues zeta_p^j, zeta_p^-j.
Then S_q(bc) = S_p(ae) = 0, 1 + ac and 1 + be kill e1, and all Artin relations hold:
(ac)^2 = (be)^2 = 1, (bc)^q = (ae)^p = 1 (diagonalisable of finite order, and the swapped products
are conjugates).  So c0 >= 1.  We solve numerically, then compute ct at random s.
Usage: python3 char0_witness.py q p [tries]
"""
import cmath
import sys

import numpy as np
from scipy.optimize import least_squares


def unpack(z):
    z = z[0::2] + 1j * z[1::2]
    a = z[0:4].reshape(2, 2)
    beta, gamma, x, y = z[4:8]
    return a, beta, gamma, x, y


def build(z):
    a, beta, gamma, x, y = unpack(z)
    I = np.eye(2)
    b = beta * I + gamma * a
    AC = np.array([[-1, x], [0, 1]])
    BE = np.array([[-1, y], [0, 1]])
    c = np.linalg.solve(a, AC)
    e = np.linalg.solve(b, BE)
    return a, b, c, e


def residual(z, q, p, i, j):
    a, b, c, e = build(z)
    zq, zp = cmath.exp(2j * cmath.pi * i / q), cmath.exp(2j * cmath.pi * j / p)
    bc, ae = b @ c, a @ e
    r = [c @ e - e @ c,
         np.array([np.trace(bc) - (zq + 1 / zq), np.linalg.det(bc) - 1]),
         np.array([np.trace(ae) - (zp + 1 / zp), np.linalg.det(ae) - 1]),
         np.array([np.linalg.det(a) - 1])]  # normalisation (scaling a by lambda, b by 1/lambda)
    r = np.concatenate([np.ravel(t) for t in r])
    return np.concatenate([r.real, r.imag])


def S(X, k):
    R = np.eye(2, dtype=complex)
    P = np.eye(2, dtype=complex)
    for _ in range(k - 1):
        P = P @ X
        R = R + P
    return R


def alt(X, Y, m):
    P = np.eye(2, dtype=complex)
    for t in range(m):
        P = P @ (X if t % 2 == 0 else Y)
    return P


def analyse(mats, q, p, rng):
    a, b, c, e = mats
    rel = max(np.abs(a @ b - b @ a).max(), np.abs(c @ e - e @ c).max(),
              np.abs(alt(a, c, 4) - alt(c, a, 4)).max(), np.abs(alt(b, c, 2 * q) - alt(c, b, 2 * q)).max(),
              np.abs(alt(b, e, 4) - alt(e, b, 4)).max(), np.abs(alt(a, e, 2 * p) - alt(e, a, 2 * p)).max())
    cross = [(a, c, 2), (b, c, q), (b, e, 2), (a, e, p)]
    Ss = [S(P @ Q, k) for P, Q, k in cross]
    sv0 = np.linalg.svd(np.vstack(Ss), compute_uv=False)
    s = complex(rng.uniform(0.3, 0.9), rng.uniform(0.2, 0.7))
    Mt = np.vstack([Sm @ (s * P - np.eye(2)) for Sm, (P, Q, k) in zip(Ss, cross)])
    svt = np.linalg.svd(Mt, compute_uv=False)
    return rel, sv0, svt


if __name__ == "__main__":
    q, p = int(sys.argv[1]), int(sys.argv[2])
    tries = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    rng = np.random.default_rng(0)
    found = 0
    for tr in range(tries):
        i = rng.integers(1, q)
        j = rng.integers(1, p)
        z0 = rng.normal(size=16)
        try:
            sol = least_squares(residual, z0, args=(q, p, i, j), xtol=1e-15, ftol=1e-15, gtol=1e-15)
        except np.linalg.LinAlgError:
            continue
        if np.abs(sol.fun).max() > 1e-11:
            continue
        mats = build(sol.x)
        rel, sv0, svt = analyse(mats, q, p, rng)
        found += 1
        print(f"try {tr} (i,j)=({i},{j}) relation defect {rel:.1e}  sigma-stack sv {np.round(sv0, 6)}"
              f"  twisted-stack sv {np.round(svt, 6)}", flush=True)
        if found >= 8:
            break
    print("solutions found:", found)
