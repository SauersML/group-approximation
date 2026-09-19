#!/usr/bin/env python3
"""Explicit spectral-matching HS models of the Baumslag--Gersten group (calibration world).

BG = <a, t | b^-1 a b = a^2, b = t^-1 a t>.  Every finite-dimensional unitary representation has
a = I (finite quotients cyclic), yet BG is sofic.  Construction in dimension m (m odd prime with 2 a
primitive root mod m):

  a = diag(zeta^k),  zeta = exp(2 pi i/m);   P e_k = e_{2k}  (so P^-1 a P = a^2 exactly);
  P has eigenvalue 1 on e_0 and the (m-1)-th roots of unity on the Fourier vectors of the orbit
  1 -> 2 -> 4 -> ...; match P's eigenvalues, in angular order, to the spectrum of a, and let t send
  the matched P-eigenvector to the matching standard basis vector.  Then b = t^-1 a t differs from
  P by the spectral mismatch E, and ||R - I||_2 <= 2 ||b - P||_2 = O(1/m).

Prints m, e(R) = ||R - I||_2^2, the proved bound 4 ||b - P||_2^2, and e([a,t]).
"""

import numpy as np


def is_prim_root2(m):
    x, seen = 1, set()
    for _ in range(m - 1):
        x = (2 * x) % m
        seen.add(x)
    return len(seen) == m - 1


def model(m):
    zeta = np.exp(2j * np.pi / m)
    a = np.diag(zeta ** np.arange(m))
    orbit = [pow(2, j, m) for j in range(m - 1)]
    vecs, angles = [np.eye(m)[:, 0]], [0.0]
    for l in range(m - 1):
        v = np.zeros(m, dtype=complex)
        for j, o in enumerate(orbit):
            v[o] = np.exp(-2j * np.pi * l * j / (m - 1))
        vecs.append(v / np.sqrt(m - 1))
        angles.append(2 * np.pi * l / (m - 1))
    order = np.argsort(angles, kind="stable")
    t = np.zeros((m, m), dtype=complex)
    Pdiag = np.zeros(m, dtype=complex)
    for k, i in enumerate(order):  # k-th smallest P-angle -> a-eigenvalue zeta^k
        t += np.outer(np.eye(m)[:, k], vecs[i].conj())
        Pdiag[k] = np.exp(1j * angles[i])
    P = np.zeros((m, m))
    for k in range(m):
        P[(2 * k) % m, k] = 1.0
    return a, t, P, Pdiag


def e(X):
    return 2 - 2 * np.real(np.trace(X)) / X.shape[0]


def main():
    print("m  e(R)  bound4||b-P||^2  e([a,t])  m^2*e(R)")
    for m in [p for p in range(3, 400) if all(p % q for q in range(2, int(p**0.5) + 1)) and is_prim_root2(p)]:
        a, t, P, Pd = model(m)
        ti = t.conj().T
        assert np.allclose(t @ ti, np.eye(m), atol=1e-9)
        assert np.allclose(np.linalg.inv(P) @ a @ P, a @ a)
        b = ti @ a @ t
        R = np.linalg.inv(b) @ a @ b @ np.linalg.inv(a @ a)
        dist2 = np.linalg.norm(b - P) ** 2 / m
        c = a @ t @ a.conj().T @ ti
        eR = e(R)
        assert eR <= 4 * dist2 + 1e-9
        print(f"{m:4d} {eR:.3e} {4*dist2:.3e} {e(c):.4f} {m*m*eR:.3f}")


if __name__ == "__main__":
    main()
