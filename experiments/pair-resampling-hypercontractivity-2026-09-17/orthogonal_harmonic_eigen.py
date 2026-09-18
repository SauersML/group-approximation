"""Degree-k spectrum of the pair-resampling walk on the rotated-frame universe
U_n (frames in O(2n)), T = E_P E_{M ~ Haar O(V_P^perp)} f(K_P(M) X).

Degree <= k polynomial functions f(X) = <t, X^{(x)k}> form a quotient of
(R^{2n})^{(x)k} (x) (R^{2n})^{(x)k}; T acts on the label factor by
A_k = E_P Proj(O(V_P^perp)-invariants), so the spectrum of A_k on the
complement of the Stab(1)-invariants bounds T on degree <= k harmonics
orthogonal to functions of s = sum_a x_a.

k = 1: Proj = Pi.  k = 2: Pi(x)Pi + Q Q^T / n.
k = 3: Pi(x)Pi(x)Pi + sum_i Pi at slot i (x) QQ^T/n on the other two slots.
Here Q = I - Pi is viewed as a tensor in V^perp (x) V^perp (norm^2 = n).
The Stab(1) = O(1^perp) invariants removed are spanned by the Brauer tensors
built from 1 and the identity: k=1: 1; k=2: 1(x)1, I; k=3: 1(x)1(x)1,
1(x)I, I(x)1 (slots), and I_{13}(x)1_2.
"""
import sys
import numpy as np
from itertools import permutations


def pairings(s):
    s = list(s)
    if not s:
        yield []
        return
    a = s[0]
    for i in range(1, len(s)):
        rest = s[1:i] + s[i + 1:]
        for p in pairings(rest):
            yield [(a, s[i])] + p


def pi_matrix(p, N):
    M = np.zeros((N, N))
    for a, b in p:
        for u in (a, b):
            for v in (a, b):
                M[u, v] = 0.5
    return M


def A_matrix(n, k):
    N = 2 * n
    I = np.eye(N)
    tot = np.zeros((N ** k, N ** k))
    count = 0
    for p in pairings(range(N)):
        Pi = pi_matrix(p, N)
        Q = (I - Pi).reshape(-1)
        QQ = np.outer(Q, Q) / n  # projection onto Q in 2 slots (norm^2 n)
        if k == 1:
            P = Pi
        elif k == 2:
            P = np.kron(Pi, Pi) + QQ
        elif k == 3:
            P = np.kron(np.kron(Pi, Pi), Pi)
            # slot 1 = Pi, slots 2,3 = QQ
            P = P + np.kron(Pi, QQ)
            # slot 3 = Pi, slots 1,2 = QQ
            P = P + np.kron(QQ, Pi)
            # slot 2 = Pi, slots 1,3 = QQ: permute axes
            B = np.kron(Pi, QQ).reshape((N,) * 6)  # (2,1,3 | 2,1,3) order
            B = B.transpose(1, 0, 2, 4, 3, 5).reshape(N ** 3, N ** 3)
            P = P + B
        tot += P
        count += 1
    return tot / count


def invariant_basis(n, k):
    N = 2 * n
    one = np.ones(N) / np.sqrt(N)
    I = np.eye(N).reshape(-1)
    vecs = []
    if k == 1:
        vecs = [one]
    elif k == 2:
        vecs = [np.kron(one, one), I]
    elif k == 3:
        t = np.kron(I, one).reshape(N, N, N)
        vecs = [np.kron(np.kron(one, one), one), np.kron(one, I), np.kron(I, one),
                t.transpose(0, 2, 1).reshape(-1)]
    B = np.array(vecs).T
    q, _ = np.linalg.qr(B)
    return q


if __name__ == '__main__':
    for n, k in [(2, 1), (3, 1), (4, 1), (2, 2), (3, 2), (4, 2), (5, 2), (2, 3), (3, 3), (4, 3)]:
        A = A_matrix(n, k)
        q = invariant_basis(n, k)
        Pc = np.eye(A.shape[0]) - q @ q.T
        ev = np.linalg.eigvalsh(Pc @ A @ Pc)
        ev = np.sort(ev)[::-1]
        # check A symmetric and invariants fixed
        fix = np.linalg.norm(A @ q - q)
        # restrict further to (1^perp)^(x)k minus the invariant I_{1^perp} (k=2)
        N = 2 * n
        C = np.eye(N) - np.ones((N, N)) / N
        Ck = C
        for _ in range(k - 1):
            Ck = np.kron(Ck, C)
        R = Ck
        if k == 2:
            v = C.reshape(-1)
            v = v / np.linalg.norm(v)
            R = Ck - np.outer(v, v)
        ev2 = np.sort(np.linalg.eigvalsh(R @ A @ R))[::-1]
        print(f"n={n} k={k} top={ev[0]:.6f} next={ev[1]:.6f} invariant-fix-err={fix:.1e} "
              f"top-on-1perp-chaos={ev2[0]:.6f} 2^-k={2.0**-k:.4f} 2^(-k/2)={2**(-k/2):.4f}",
              flush=True)
