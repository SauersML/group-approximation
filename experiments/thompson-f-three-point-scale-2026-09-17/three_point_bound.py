#!/usr/bin/env python3
"""Three-point projection bound for size-only test vectors of Thompson's F in the log-scale limit (E2).

Setting: (E2) of thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit.  Rescaled log-sizes
X_j in [0,1] form an arbitrary stationary process (any memory, hidden states, hierarchies) with
atomless marginal; merge acts as max; a split of level m has one child of level m and one of level s<m.

Projection lemma: projecting both the merged image and the target onto (side, s, m, the neighbour on
the side of the small child) can only raise the Bhattacharyya affinity, so B <= Phi(P3), where P3 is the
3-point law of (X_{-1}, X_0, X_1) and, with p2 the 2-point law,

  Phi = int dm sqrt( int_{s<m} ds [ c_L(s,m)^2 + c_R(s,m)^2 ] ),
  c_L(s,m) = int da sqrt(p3(a,s,m) p2(a,m)),   c_R(s,m) = int db sqrt(p3(m,s,b) p2(m,b)).

Every stationary P3 is the 3-marginal of an order-2 chain, so sup_P3 Phi bounds B for ALL stationary
size processes.  Here P3 is piecewise constant on N bins (the process: order-2 chain on bins, independent
uniform jitter inside bins); the bin formula is exact for such laws.

Modes:
  check        : Phi == scale_B on random order-1 kernels (Phi is lossless for Markov chains).
  opt N...     : maximise Phi over order-2 bin kernels (L-BFGS, several starts).
"""
import sys
import os
import torch

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', 'thompson-f-markov-forest-2026-09-17'))
from scale_limit import scale_B          # noqa: E402
from markov_ansatz import stationary     # noqa: E402

torch.set_default_dtype(torch.float64)


def pair_stationary(K2):
    """K2[a,b,c] = P(X_1=c | X_{-1}=a, X_0=b).  Return stationary law Pi[a,b] of the pair chain."""
    N = K2.shape[0]
    T = torch.zeros(N * N, N * N)
    # state (a,b) -> (b,c)
    idx_ab = torch.arange(N * N)
    a = idx_ab // N
    b = idx_ab % N
    for c in range(N):
        T[idx_ab, b * N + c] = K2[a, b, c]
    return stationary(T).reshape(N, N)


def phi_from_P3(P3):
    N = P3.shape[0]
    Q = P3.sum(2)                    # Q[i,k] = P(X_{-1}=i, X_0=k) = P(X_0=i, X_1=k)
    # c_L[j,k] = sum_i sqrt(P3[i,j,k] Q[i,k])
    cL = torch.sqrt((P3 * Q.unsqueeze(1)).clamp_min(0)).sum(0)
    # c_R[j,k] = sum_b sqrt(P3[k,j,b] Q[k,b])  -> tensor over (k,j,b)
    cR = torch.sqrt((P3 * Q.unsqueeze(1)).clamp_min(0)).sum(2).T
    C = cL ** 2 + cR ** 2            # C[j,k], j = bin of small child s, k = bin of m
    low = torch.triu(torch.ones(N, N), diagonal=1)
    A = (C * low).sum(0)
    d = torch.diagonal(C).clamp_min(1e-300)
    return ((2.0 / 3.0) * ((A + d) ** 1.5 - A ** 1.5) / d).sum()


def phi_order2(K2):
    Pi = pair_stationary(K2)
    P3 = Pi.unsqueeze(2) * K2
    return phi_from_P3(P3)


def check():
    torch.manual_seed(1)
    worst = 0.0
    for N in [2, 3, 4, 6, 8]:
        for t in range(5):
            K = torch.softmax(torch.randn(N, N) * (1 + t), 1)
            pi = stationary(K)
            P3 = pi[:, None, None] * K[:, :, None] * K[None, :, :]
            v1 = phi_from_P3(P3).item()
            v2 = scale_B(K).item()
            K2 = K.unsqueeze(0).expand(N, N, N).clone()
            v3 = phi_order2(K2).item()
            worst = max(worst, abs(v1 - v2), abs(v3 - v2))
    print("check: max |Phi - scale_B| over 25 order-1 kernels = %.2e" % worst)
    # product kernel gives 2 sqrt2/3
    N = 16
    K = torch.full((N, N), 1.0 / N)
    print("check: product N=16 Phi = %.12f (2sqrt2/3 = %.12f)" % (
        phi_order2(K.unsqueeze(0).expand(N, N, N).clone()).item(), 2 * 2 ** 0.5 / 3))
    # random order-2 kernels: Phi <= E sqrt(U+D) <= 1 sanity
    mx = 0.0
    for t in range(50):
        N = 5
        K2 = torch.softmax(torch.randn(N, N, N) * 3, 2)
        mx = max(mx, phi_order2(K2).item())
    print("check: max Phi on 50 random order-2 kernels (N=5) = %.6f  (must be <= 1)" % mx)


def lbfgs(f, x, iters):
    x = x.clone().requires_grad_(True)
    o = torch.optim.LBFGS([x], max_iter=iters, line_search_fn='strong_wolfe', tolerance_grad=1e-11,
                          tolerance_change=1e-13, history_size=50)

    def closure():
        o.zero_grad()
        v = -f(x)
        v.backward()
        return v
    o.step(closure)
    return f(x).item(), x.detach()


def optimise(N, starts=4, iters=3000, seed=0):
    torch.manual_seed(seed)
    best, bestx = -1.0, None
    for t in range(starts):
        x0 = (0.3 + 0.7 * t) * torch.randn(N, N, N)
        v, x = lbfgs(lambda z: phi_order2(torch.softmax(z, 2)), x0, iters)
        print("N=%d start %d  Phi=%.6f  R-bound=(1+Phi)/2=%.6f" % (N, t, v, (1 + v) / 2), flush=True)
        if v > best:
            best, bestx = v, x
    print("N=%d best Phi=%.6f" % (N, best), flush=True)
    return best, bestx


if __name__ == "__main__":
    if len(sys.argv) < 2 or sys.argv[1] == "check":
        check()
    elif sys.argv[1] == "opt":
        Ns = [int(a) for a in sys.argv[2:]] or [3, 4, 6, 8]
        for N in Ns:
            b, x = optimise(N)
            torch.save(torch.softmax(x, 2), os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                        "best_K2_N%d.pt" % N))
