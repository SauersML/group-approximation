"""Evaluate the Lochak--Schneps relators r_1, r_2 on every SL_2(C) lift of a
Delta(4,3,5) character (rigid: the character is fixed by the three traces).

tr A = 2cos(k pi/4), tr B = +-2cos(j pi/3), tr BA = +-2cos(l pi/5).
Output: for each character, whether A^4, B^3, (BA)^5 are +-1 and tr r_1, tr r_2.
"""
import itertools
import numpy as np


def pair(x, y, z):
    A = np.array([[x, 1], [-1, 0]], dtype=complex)
    t = np.roots([1, z, 1])[0]          # tr(AB) = -(t + 1/t) = z
    B = np.array([[0, t], [-1 / t, y]], dtype=complex)
    return A, B


def comm(P, Q):
    return P @ Q @ np.linalg.inv(P) @ np.linalg.inv(Q)


def pm1(M):
    return np.allclose(M, np.eye(2)) or np.allclose(M, -np.eye(2))


def main():
    for k, j, l in itertools.product([1, 3], [1, 2], [1, 2, 3, 4]):
        for sb, sp in itertools.product([1, -1], [1, -1]):
            x = 2 * np.cos(np.pi * k / 4)
            y = sb * 2 * np.cos(np.pi * j / 3)
            z = sp * 2 * np.cos(np.pi * l / 5)
            A, B = pair(x, y, z)
            BA = B @ A
            if not (pm1(np.linalg.matrix_power(A, 4)) and pm1(np.linalg.matrix_power(B, 3))
                    and pm1(np.linalg.matrix_power(BA, 5))):
                continue
            X = B @ A @ B
            J = A @ A
            W = J @ B @ B @ J
            r1 = comm(X, J @ X @ np.linalg.inv(J))
            r2 = comm(X, W @ X @ np.linalg.inv(W))
            kappa = np.trace(comm(A, B)).real   # >2: real hyperbolic (PSL2R); <2: SU(2) type
            print(f"k={k} j={j} l={l} sb={sb:+d} sp={sp:+d}  tr[A,B]={kappa:+.4f}  "
                  f"r1: pm1={pm1(r1)} tr={np.trace(r1).real:+.6f}  "
                  f"r2: pm1={pm1(r2)} tr={np.trace(r2).real:+.6f}")


if __name__ == "__main__":
    main()
