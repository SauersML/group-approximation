#!/usr/bin/env python3
"""Floating-point scouting: i.i.d. tree-stack ansatz with multiplicative split weights.

iid_ansatz.py (all shapes, N <= 10) converges to an optimum of the exact form
    x(T) = phi(|L|,|R|) x(L) x(R),        x(leaf) = x1,
    y(T) = g(|L|,|R|)   y(L) x(R),        y(leaf) = y1,
for T = (L, R).  Summing over shapes, with A_n = sum x^2, Bq_n = sum y^2, X_n = sum x y over the
trees with n leaves:
    A_n  = sum_{l+r=n} phi^2 A_l A_r,   Bq_n = sum g^2 Bq_l A_r,   X_n = sum phi g X_l A_r,
    Merge_n = sum_{T} y(L) x(R) y(T) = sum g Bq_l A_r,
and the per-site Rayleigh quotient is
    R = 2 (sum X)^2 / (sum A * sum Bq) + 2 sum Merge / (sqrt(sum A) * sum Bq).
Optimised with torch L-BFGS over log phi, log g (N(N-1)/2 each) and log x1, log y1.
Output: R/4 and the sufficient statistics used by window_split.py.
"""
import sys, json
import torch

torch.set_default_dtype(torch.float64)


def stats(lphi, lg, lx1, ly1, N):
    A = [None, torch.exp(2 * lx1)]
    Bq = [None, torch.exp(2 * ly1)]
    X = [None, torch.exp(lx1 + ly1)]
    M = [None, torch.zeros(())]
    for n in range(2, N + 1):
        l = torch.arange(1, n)
        ph = torch.exp(lphi[l, n - l])
        gg = torch.exp(lg[l, n - l])
        Al = torch.stack(A[1:n])
        Ar = torch.flip(Al, [0])
        Bl = torch.stack(Bq[1:n])
        Xl = torch.stack(X[1:n])
        A.append(torch.sum(ph ** 2 * Al * Ar))
        Bq.append(torch.sum(gg ** 2 * Bl * Ar))
        X.append(torch.sum(ph * gg * Xl * Ar))
        M.append(torch.sum(gg * Bl * Ar))
    return [torch.stack(v[1:]) for v in (A, Bq, X, M)]


def rq(params, N):
    A, Bq, X, M = stats(*params, N)
    sA, sB = A.sum(), Bq.sum()
    return 2 * X.sum() ** 2 / (sA * sB) + 2 * M.sum() / (torch.sqrt(sA) * sB)


def optimise(N, iters=60, init=None):
    lphi = torch.zeros(N + 1, N + 1)
    lg = torch.zeros(N + 1, N + 1)
    lx1 = torch.tensor(-0.4)
    ly1 = torch.tensor(-0.6)
    if init is not None:
        m = init[0].shape[0]
        lphi[:m, :m] = init[0]
        lg[:m, :m] = init[1]
        lx1, ly1 = init[2].clone(), init[3].clone()
    params = [lphi.requires_grad_(), lg.requires_grad_(), lx1.requires_grad_(), ly1.requires_grad_()]
    opt = torch.optim.LBFGS(params, lr=1, max_iter=50, history_size=50, line_search_fn='strong_wolfe')
    best = 0
    for it in range(iters):
        def closure():
            opt.zero_grad()
            loss = -rq(params, N)
            loss.backward()
            return loss
        opt.step(closure)
        r = rq(params, N).item()
        if abs(r - best) < 1e-11:
            break
        best = r
    return best, [p.detach() for p in params]


if __name__ == "__main__":
    Ns = [int(a) for a in sys.argv[1:]] or [9, 20, 40]
    init = None
    out = {}
    for N in Ns:
        r, params = optimise(N, init=init)
        init = params
        A, Bq, X, M = stats(*params, N)
        sA, sB = A.sum().item(), Bq.sum().item()
        a = (A / sA).tolist()
        mean = sum((k + 1) * a[k] for k in range(N))
        print(f"N={N} R={r:.7f} R/4={r/4:.7f} a(size1)={a[0]:.4f} mean size={mean:.2f} "
              f"a(size N)={a[-1]:.2e}", flush=True)
        out[N] = {"R_over_4": r / 4}
        torch.save(params, f"split_params_N{N}.pt")
    json.dump(out, open("split_ansatz.json", "w"), indent=1)
