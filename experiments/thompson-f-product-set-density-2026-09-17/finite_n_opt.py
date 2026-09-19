#!/usr/bin/env python3
"""Float scout (not used by any proof): the FINITE-n relaxation for product indicator window sets.

For a product indicator family (A_s = |cal A_s|, B_s = |cal B_s|) the window set Y_n has
    |Y_n|      = sum_s B_s Y_{n-s},
    #shift     = sum_{s,t} X_s X_t Y_{n-s-t},     X_s <= min(A_s, B_s),
    #merge     = sum_m E_m Y_{n-m},               E_m <= min(B_m, (B*A)_m),
where W is the renewal sequence of A (W_0 = 1, W_l = sum_s A_s W_{l-s}) and Y = W * W.
density(Y_n) = 2 (#shift + #merge) / |Y_n|.  We maximize the relaxation with X, E at their caps,
over positive reals A_s, B_s (s <= n), dropping the Catalan and integrality limits (which only
enlarges the feasible set).

Usage: finite_n_opt.py n [restarts] [steps]
"""
import sys
import torch

torch.set_default_dtype(torch.float64)


def density(la, lb, n):
    A = torch.exp(la)  # index k <-> size k+1, k = 0..n-1
    B = torch.exp(lb)
    W = [torch.ones(())]
    for l in range(1, n + 1):
        W.append(sum(A[s - 1] * W[l - s] for s in range(1, l + 1)))
    W = torch.stack(W)
    Y = torch.stack([sum(W[l] * W[k - l] for l in range(k + 1)) for k in range(n + 1)])
    X = torch.minimum(A, B)
    D = sum(B[s - 1] * Y[n - s] for s in range(1, n + 1))
    sh = sum(X[s - 1] * X[t - 1] * Y[n - s - t] for s in range(1, n) for t in range(1, n - s + 1))
    me = 0
    for m in range(2, n + 1):
        ba = sum(B[k - 1] * A[m - k - 1] for k in range(1, m))
        me = me + torch.minimum(B[m - 1], ba) * Y[n - m]
    return 2 * (sh + me) / D


def run(n, restarts, steps, seed=1):
    g = torch.Generator().manual_seed(seed)
    best = -1
    arg = None
    for r in range(restarts):
        la = (torch.randn(n, generator=g) + torch.arange(n) * 0.0).requires_grad_()
        lb = (torch.randn(n, generator=g)).requires_grad_()
        opt = torch.optim.Adam([la, lb], lr=0.05)
        for t in range(steps):
            opt.zero_grad()
            d = density(la, lb, n)
            (-d).backward()
            opt.step()
        with torch.no_grad():
            d = density(la, lb, n).item()
        if d > best:
            best, arg = d, (la.detach().clone(), lb.detach().clone())
    return best, arg


if __name__ == '__main__':
    n = int(sys.argv[1])
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    T = int(sys.argv[3]) if len(sys.argv) > 3 else 1500
    best, (la, lb) = run(n, R, T)
    print('n=%d  sup density (relaxation, float) ~ %.5f' % (n, best))
    print('log A:', ' '.join('%.2f' % x for x in la.tolist()))
    print('log B:', ' '.join('%.2f' % x for x in lb.tolist()))
