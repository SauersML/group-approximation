#!/usr/bin/env python3
"""Floating-point scouting: the i.i.d. tree-stack ansatz restricted to size-only weights.

iid_ansatz.py shows numerically (N <= 10) that the optimal x = sqrt(a), y = sqrt(b) depend on a
tree only through its number of leaves.  With p_n = a(size n), q_n = b(size n) (probabilities on
sizes, uniform over the Cat(n-1) shapes of each size) the per-site Rayleigh quotient is

  R(p,q) = 2 (sum_n sqrt(p_n q_n))^2 + 2 sum_{k,l} c_{k,l} sqrt(q_k p_l q_{k+l}),
  c_{k,l} = sqrt(Cat(k-1) Cat(l-1) / Cat(k+l-1)).

Alternating maximisation: for fixed u = sqrt(p) the best v = sqrt(q) is the Perron vector of
2 u u^T + (M_u + M_u^T), M_u[k+l, k] = c_{k,l} u_l; for fixed v the best u is a normalised
combination of v and w_v, w_v[l] = sum_k c_{k,l} v_k v_{k+l}.
"""
import sys
import numpy as np
from scipy.special import gammaln
from scipy.sparse.linalg import LinearOperator, eigsh


def logcat(m):  # log Catalan(m)
    return gammaln(2 * m + 1) - gammaln(m + 2) - gammaln(m + 1)


def setup(N):
    n = np.arange(1, N + 1)
    lc = logcat(n - 1)
    K, L = np.meshgrid(n, n, indexing='ij')
    ok = K + L <= N
    C = np.zeros((N + 1, N + 1))  # C[k, l], 1-based
    C[1:, 1:] = np.where(ok, np.exp(0.5 * (lc[K - 1] + lc[L - 1] - lc[np.minimum(K + L, N) - 1])), 0.0)
    return C


def R(u, v, C):
    N = len(u) - 1
    s = 0.0
    for k in range(1, N):
        l = np.arange(1, N - k + 1)
        s += np.sum(C[k, l] * v[k] * u[l] * v[k + l])
    return 2 * (u @ v) ** 2 + 2 * s


def best_v(u, C):
    N = len(u) - 1

    def mv(z):
        out = 2 * u * (u @ z)
        for k in range(1, N):
            l = np.arange(1, N - k + 1)
            out[k + l] += C[k, l] * u[l] * z[k]
            out[k] += np.sum(C[k, l] * u[l] * z[k + l])
        return out
    op = LinearOperator((N + 1, N + 1), matvec=mv, dtype=float)
    w, vec = eigsh(op, k=1, which='LA', tol=1e-12)
    vec = np.abs(vec[:, 0])
    vec[0] = 0
    return vec / np.linalg.norm(vec)


def best_u(v, C):
    N = len(v) - 1
    w = np.zeros(N + 1)
    for k in range(1, N):
        l = np.arange(1, N - k + 1)
        w[l] += C[k, l] * v[k] * v[k + l]
    # maximise 2 (u.v)^2 + 2 u.w over unit u in span(v, w): exact 2x2 problem
    e1 = v / np.linalg.norm(v)
    w2 = w - (w @ e1) * e1
    nw = np.linalg.norm(w2)
    if nw < 1e-300:
        return e1
    e2 = w2 / nw
    th = np.linspace(-np.pi / 2, np.pi / 2, 20001)
    val = 2 * np.cos(th) ** 2 + 2 * (np.cos(th) * (w @ e1) + np.sin(th) * (w @ e2))
    t = th[np.argmax(val)]
    u = np.cos(t) * e1 + np.sin(t) * e2
    return np.abs(u)


def optimise(N, iters=300, verbose=False):
    C = setup(N)
    n = np.arange(N + 1)
    u = np.where(n > 0, 0.5 ** n, 0.0)
    u /= np.linalg.norm(u)
    last = 0
    for it in range(iters):
        v = best_v(u, C)
        u = best_u(v, C)
        r = R(u, v, C)
        if abs(r - last) < 1e-13:
            break
        last = r
    return r, u, v


if __name__ == "__main__":
    for N in [int(a) for a in sys.argv[1:]] or [10]:
        r, u, v = optimise(N)
        p, q = u ** 2, v ** 2
        n = np.arange(N + 1)
        print(f"N={N} R={r:.7f} R/4={r/4:.7f} p1={p[1]:.4f} q1={q[1]:.4f} "
              f"mean p={p@n:.3f} mean q={q@n:.3f} tail p[N]={p[-1]:.2e} q[N]={q[-1]:.2e}", flush=True)
