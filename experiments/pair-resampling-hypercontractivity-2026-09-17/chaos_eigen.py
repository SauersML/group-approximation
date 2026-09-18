"""Top eigenvalue of T_k = E_P Pi_P^{(x)k} on (1^perp)^{(x)k}, R^{2n}.

Pi_P is the pair-averaging projection of a perfect pairing P of [2n].
Compare with 2^{-k/2}, i.e. domination by the Ornstein-Uhlenbeck operator
with correlation 1/sqrt(2)."""
import sys
import numpy as np
from scipy.sparse.linalg import LinearOperator, eigsh


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


def partner(p, N):
    q = np.empty(N, dtype=int)
    for a, b in p:
        q[a] = b
        q[b] = a
    return q


def center(t, k):
    for ax in range(k):
        t = t - t.mean(axis=ax, keepdims=True)
    return t


def top(n, k, nev=3):
    N = 2 * n
    Ps = [partner(p, N) for p in pairings(range(N))]
    shape = (N,) * k

    def mv(v):
        t = center(v.reshape(shape), k)
        out = np.zeros(shape)
        for q in Ps:
            s = t
            for ax in range(k):
                s = 0.5 * (s + np.take(s, q, axis=ax))
            out += s
        return center(out / len(Ps), k).ravel()

    op = LinearOperator((N ** k, N ** k), matvec=mv, dtype=float)
    w = eigsh(op, k=nev, which='LA', return_eigenvectors=False, tol=1e-9)
    return sorted(w)[::-1]


if __name__ == '__main__':
    cases = [(2, 6), (3, 5), (4, 4), (5, 3)]
    if len(sys.argv) > 1:
        cases = [tuple(map(int, a.split(','))) for a in sys.argv[1:]]
    for n, kmax in cases:
        for k in range(1, kmax + 1):
            ev = top(n, k)
            b = 2 ** (-k / 2)
            print(f"n={n} k={k} top={ev[0]:.6f} 2nd={ev[1]:.6f} "
                  f"2^(-k/2)={b:.6f} ratio={ev[0] / b:.4f}", flush=True)
