#!/usr/bin/env python3
"""Size-level merge functional for stationary Markov size processes (an upper-bound proxy).

For any f >= 0 on pointed-forest windows, pi = f^2 / D is a probability law on pointed forests and
    <f, K f> / (4 <f,f>) = [BC(pi, shift_* pi) + BC(pi, merge_* pi)] / 2
(the reverse edges pair up).  Pushing pi forward to the size sequence seen from the pointer can
only increase each Bhattacharyya coefficient (data processing), so the Rayleigh quotient of f is at
most the same expression computed on the size process.  When the size process is a stationary
Markov chain with transition P on {1..K} and stationary law mu, the shift term is 1 and
    BC_merge(P) = sum_{x,y,z} mu(x) sqrt( P(x,y) P(y,z) * sum_{a+b=y} P(x,a) P(a,b) P(b,z) ).
For P(x, .) = alpha this is BC(alpha, alpha * alpha).  We maximise BC_merge over P by L-BFGS.
Usage: python markov_size_level.py K [seed]
"""
import sys
import torch

torch.set_default_dtype(torch.float64)


def bc_merge(logits):
    K = logits.shape[0]
    P = torch.softmax(logits, dim=1)                   # P[x, y], sizes y = 1..K (index y-1)
    # stationary law
    mu = torch.ones(K) / K
    for _ in range(300):
        mu = mu @ P
    mu = mu / mu.sum()
    # C[x, y, z] = sum_{a+b=y} P(x,a) P(a,b) P(b,z)
    C = torch.zeros(K, K, K)
    for y in range(2, K + 1):
        a = torch.arange(1, y)
        b = y - a
        # sum_a P[x,a-1] * P[a-1,b-1] * P[b-1, z]
        t = P[:, a - 1] * P[a - 1, b - 1][None, :]      # (x, #a)
        C[:, y - 1, :] = t @ P[b - 1, :]
    D = P[:, :, None] * P[None, :, :]                   # P(x,y) P(y,z)
    return (mu[:, None, None] * torch.sqrt(D * C + 1e-300)).sum()


if __name__ == "__main__":
    K = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    g = torch.Generator().manual_seed(seed)
    # iid start: alpha ~ geometric-ish
    L = (-0.3 * torch.arange(K, dtype=torch.float64))[None, :].repeat(K, 1) + 0.5 * torch.randn(K, K, generator=g)
    L.requires_grad_()
    opt = torch.optim.LBFGS([L], lr=1, max_iter=50, history_size=50, line_search_fn='strong_wolfe')
    best = 0
    for it in range(200):
        def closure():
            opt.zero_grad(); loss = -bc_merge(L); loss.backward(); return loss
        opt.step(closure)
        v = bc_merge(L).item()
        if it % 10 == 0 or abs(v - best) < 1e-11:
            print(f"K={K} it={it} BC_merge={v:.8f} quotient bound=(1+BC)/2={(1+v)/2:.8f}", flush=True)
        if abs(v - best) < 1e-11:
            break
        best = v
    torch.save(L.detach(), f"markov_size_K{K}_s{seed}.pt")
