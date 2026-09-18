"""T_3 recheck: zeros of a_n(z)=E z^|X_n| inside |z-1/2|<0.25 as n grows.

The disc contains p_2(T_3)=1/sqrt2=0.7071, where the flat rate ends, so the
pinch lemma predicts zeros entering it for large n.
"""
import numpy as np


def law(n):
    q = np.zeros(n + 2)
    q[0] = 1.0
    for _ in range(n):
        nq = np.zeros_like(q)
        nq[1] += q[0]
        nq[2:] += (2 / 3) * q[1:-1]
        nq[0:-1] += np.concatenate([[1 / 3 * q[1]], (1 / 3) * q[2:]])
        q = nq
    return q


def a(z, q):
    s = np.zeros_like(z)
    for k in range(len(q) - 1, -1, -1):  # Horner
        s = s * z + q[k]
    return s


def count(n, c, rad, M=20000):
    t = np.linspace(0, 2 * np.pi, M + 1)
    z = c + rad * np.exp(1j * t)
    v = a(z, law(n))
    d = np.angle(v[1:] / v[:-1])
    return np.sum(d) / (2 * np.pi), np.max(np.abs(d))


if __name__ == "__main__":
    for n in (100, 200, 400, 800, 1600, 3200):
        w, j = count(n, 0.5, 0.25)
        w2, j2 = count(n, 0.5, 0.18)
        print(f"n={n:5d}: zeros in |z-1/2|<0.25: {w:+.2f} (jump {j:.2f});"
              f" in |z-1/2|<0.18: {w2:+.2f} (jump {j2:.2f})")
