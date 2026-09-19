#!/usr/bin/env python3
"""Check that the scale-limit value of scale_limit.py is the M -> infinity limit of the exact discrete
Markov formula of markov_ansatz.py.

Take the optimal N-bin kernel Kb of scale_limit.py.  Lift it to sizes 1..M: size n lies in bin
I(n) = floor(N log n / log(M+1)), and K(n, n') = Kb[I(n), I(n')] * (1/n') / Z(I(n')), where Z(J) is the
sum of 1/n' over bin J (log-uniform inside a bin).  Then compute the discrete merge_bc(K) for growing M.
Same for a product kernel (every row = the bin-level stationary law) against 2 sqrt(2)/3.
"""
import math
import torch
from markov_ansatz import merge_bc, opt
from scale_limit import scale_B

torch.set_default_dtype(torch.float64)


def lift(Kb, M):
    N = Kb.shape[0]
    n = torch.arange(1, M + 1, dtype=torch.float64)
    I = torch.clamp((N * torch.log(n) / math.log(M + 1)).floor().long(), max=N - 1)
    w = 1.0 / n
    Z = torch.zeros(N).index_add_(0, I, w)
    ok = Z > 0
    col = w / Z[I]
    K = Kb[I][:, I] * col.unsqueeze(0)
    K = K / K.sum(1, keepdim=True)  # renormalise (only matters if a bin is empty)
    return K


def lifted_bc_fast(Kb, M):
    """Exact merge_bc(lift(Kb, M)) in O(M^2) time and O(M) memory, using the bin structure:
    beta_k(m) = sqrt(col(k) col(m) col(m-k)) * C[I(k), I(m-k), I(m)],
    C[I,J,L] = g[I,L] * sqrt(Kb[I,J]) * h[J,L],  g = S^T diag(pib) S,  h = S S^T,  S = sqrt(Kb)."""
    import numpy as np
    from markov_ansatz import stationary
    Kb = Kb.detach().numpy()
    N = Kb.shape[0]
    pib = stationary(torch.tensor(Kb)).numpy()
    S = np.sqrt(Kb)
    g = S.T @ (pib[:, None] * S)
    h = S @ S.T
    C2 = (g[:, None, :] * S[:, :, None] * h[None, :, :]) ** 2      # C[I,J,L]^2
    n = np.arange(1, M + 1, dtype=np.float64)
    I = np.minimum(np.floor(N * np.log(n) / math.log(M + 1)).astype(int), N - 1)
    w = 1.0 / n
    Z = np.bincount(I, weights=w, minlength=N)
    col = w / Z[I]
    tot = 0.0
    for m in range(2, M + 1):
        k = np.arange(1, m)
        j = m - k
        s = (col[k - 1] * col[j - 1] * C2[I[k - 1], I[j - 1], I[m - 1]]).sum()
        tot += math.sqrt(col[m - 1] * s)
    return tot


if __name__ == "__main__" and len(__import__('sys').argv) > 1:
    torch.manual_seed(0)
    Kb5 = torch.softmax(torch.randn(5, 5), 1)
    print("cross-check fast vs dense at M=200:", lifted_bc_fast(Kb5, 200), merge_bc(lift(Kb5, 200)).item())
    N = 8
    v, L = opt(lambda z: scale_B(torch.softmax(z, 1)), 0.5 * torch.randn(N, N), iters=3000)
    Kb = torch.softmax(L, 1)
    Kp = torch.ones(N, N) / N
    for M in [int(a) for a in __import__('sys').argv[1:]]:
        print("M=%7d  fast lifted: markov %.6f   product %.6f" %
              (M, lifted_bc_fast(Kb, M), lifted_bc_fast(Kp, M)), flush=True)
elif __name__ == "__main__":
    torch.manual_seed(0)
    N = 8
    v, L = opt(lambda z: scale_B(torch.softmax(z, 1)), 0.5 * torch.randn(N, N), iters=3000)
    Kb = torch.softmax(L, 1)
    Kp = torch.ones(N, N) / N
    print("N=%d scale-limit B: markov %.6f   product %.6f" % (N, v, scale_B(Kp).item()), flush=True)
    for M in [100, 300, 1000, 3000]:
        print("M=%5d  discrete merge_bc: lifted markov %.6f   lifted product %.6f" %
              (M, merge_bc(lift(Kb, M)).item(), merge_bc(lift(Kp, M)).item()), flush=True)
