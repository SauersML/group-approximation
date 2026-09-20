#!/usr/bin/env python3
"""Float scouting: maximise the stationary Rayleigh quotient of the bond-dimension-q forest ansatz
(mps_forest.py), warm-started from the q = 1 split-form optimum embedded as rank-one matrices c*J/q
plus noise.  Usage: python opt_mps.py N q noise seed [iters]"""
import sys, math, time
import torch
from mps_forest import stationary_ratio

torch.set_default_dtype(torch.float64)
N, q, noise, seed = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
iters = int(sys.argv[5]) if len(sys.argv) > 5 else 30
lphi, lg, lx1, ly1 = torch.load(f"../thompson-f-norm-ansatz-2026-09-17/split_params_N{N}.pt")
g = torch.Generator().manual_seed(seed)
lq = math.log(q)


def emb(t, shape):
    return t[..., None, None] - lq + noise * torch.randn(*shape, generator=g)


P = {'lPhi': emb(lphi, (N + 1, N + 1, q, q)), 'lGam': emb(lg, (N + 1, N + 1, q, q)),
     'lX1': emb(lx1, (q, q)), 'lY1': emb(ly1, (q, q)), 'lR': emb(torch.tensor(0.0), (q, q))}
for k in P:
    P[k] = P[k].clone().requires_grad_()
params = list(P.values())
r0 = stationary_ratio(P, N).item()
print(f"N={N} q={q} noise={noise} start R/4={r0/4:.8f}", flush=True)
opt = torch.optim.LBFGS(params, lr=1, max_iter=25, history_size=50, line_search_fn='strong_wolfe')
best = 0
t0 = time.time()
for it in range(iters):
    def closure():
        opt.zero_grad()
        loss = -stationary_ratio(P, N)
        loss.backward()
        return loss
    opt.step(closure)
    r = stationary_ratio(P, N).item()
    print(f"  it={it} R/4={r/4:.8f} t={time.time()-t0:.0f}s", flush=True)
    if abs(r - best) < 1e-10:
        break
    best = r
torch.save({k: v.detach() for k, v in P.items()}, f"mps_params_N{N}_q{q}_s{seed}.pt")
