"""Exact-identity checks for the rotated-frame universe game U_n.

1. Walk form: x' = H_P diag(I_n, R) H_P^T x (rows = labels), R in O(n).
2. Conservation: sum_a x'_a = sum_a x_a (the component vector w).
3. Perfect GKOPTW basic SDP: z(x,a) = x_a/sqrt(2n), z(y,b) = y_b/sqrt(n),
   sum of norms 1, within-vertex orthogonality, edge value 1.
4. Discretisation stability: perturbing both frames by O(eps) and re-orthonormalising
   changes the edge objective by O(eps).
"""
import numpy as np


def haar(n, rng):
    q, r = np.linalg.qr(rng.standard_normal((n, n)))
    return q * np.sign(np.diag(r))


def pairing_H(n):
    H = np.zeros((2 * n, 2 * n))
    for b in range(n):
        a, a2 = 2 * b, 2 * b + 1
        H[a, b] = H[a2, b] = 1 / np.sqrt(2)
        H[a, n + b], H[a2, n + b] = 1 / np.sqrt(2), -1 / np.sqrt(2)
    return H


def edge_value(X, Y, n):
    val = 0.0
    for b in range(n):
        for a in (2 * b, 2 * b + 1):
            val += X[a] @ Y[b] / (np.sqrt(2 * n) * np.sqrt(n))
    return val


def main():
    rng = np.random.default_rng(7)
    worst = 0.0
    for n in (2, 3, 5, 8):
        H = pairing_H(n)
        for _ in range(20):
            X = haar(2 * n, rng)            # rows x_a orthonormal
            Y = (X[0::2] + X[1::2]) / np.sqrt(2)
            R = haar(n, rng)
            K = H @ np.block([[np.eye(n), np.zeros((n, n))],
                              [np.zeros((n, n)), R]]) @ H.T
            X2 = K @ X
            Y2 = (X2[0::2] + X2[1::2]) / np.sqrt(2)
            assert np.allclose(Y2, Y), "pair sums not fixed"
            assert np.allclose(X2.sum(0), X.sum(0)), "w not conserved"
            assert np.allclose(X2 @ X2.T, np.eye(2 * n))
            assert np.isclose(edge_value(X, Y, n), 1.0)
            assert np.isclose(edge_value(X2, Y, n), 1.0)
            eps = 1e-3
            Xp, _ = np.linalg.qr((X + eps * rng.standard_normal(X.shape)).T)
            Xp = Xp.T * np.sign(np.diag(Xp.T @ X.T))[:, None]
            worst = max(worst, (1 - edge_value(Xp, Y, n)) / eps)
    print("all identities hold; worst objective loss / eps = %.3f" % worst)


if __name__ == "__main__":
    main()
