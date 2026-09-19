#!/usr/bin/env python3
"""Scan K: max of BC_merge over stationary Markov size chains on {1..K} versus over i.i.d. laws
(P(x, .) = alpha for all x, where BC_merge = BC(alpha, alpha*alpha)).  Warm-starts K from K/2.
Usage: python markov_vs_iid_scan.py K1 K2 ..."""
import sys, time
import torch
from markov_size_level import bc_merge

torch.set_default_dtype(torch.float64)


def maximise(L, fn, iters=300):
    L = L.clone().requires_grad_()
    opt = torch.optim.LBFGS([L], lr=1, max_iter=50, history_size=50, line_search_fn='strong_wolfe')
    best = 0
    for it in range(iters):
        def closure():
            opt.zero_grad(); loss = -fn(L); loss.backward(); return loss
        opt.step(closure)
        v = fn(L).item()
        if abs(v - best) < 1e-11:
            break
        best = v
    return best, L.detach()


def iid_fn(K):
    return lambda a: bc_merge(a[None, :].repeat(K, 1))


def extend_rows(Lm, K):
    m = Lm.shape[-1]
    idx = torch.clamp((torch.arange(K) * m) // K, max=m - 1)
    if Lm.dim() == 1:
        return Lm[idx]
    return Lm[idx][:, idx]


if __name__ == "__main__":
    Ks = [int(a) for a in sys.argv[1:]]
    a = None; L = None
    for K in Ks:
        t = time.time()
        a0 = -0.3 * torch.arange(K, dtype=torch.float64) if a is None else extend_rows(a, K)
        vi, a = maximise(a0, iid_fn(K))
        L0 = a[None, :].repeat(K, 1) + 0.05 * torch.randn(K, K) if L is None else extend_rows(L, K)
        L0 = torch.maximum(L0, a[None, :].repeat(K, 1)) if L is None else L0
        vm, L = maximise(L0, bc_merge)
        vm2, L2 = maximise(a[None, :].repeat(K, 1) + 0.05 * torch.randn(K, K), bc_merge)
        if vm2 > vm:
            vm, L = vm2, L2
        print(f"K={K} iid BC={vi:.7f} -> {(1+vi)/2:.7f} | markov BC={vm:.7f} -> {(1+vm)/2:.7f} "
              f"| t={time.time()-t:.0f}s", flush=True)
        torch.save({'iid': a, 'markov': L}, f"scan_K{K}.pt")
