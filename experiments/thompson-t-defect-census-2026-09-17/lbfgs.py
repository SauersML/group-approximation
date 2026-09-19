"""L-BFGS minimisation of Frobenius, then Schatten-p, relator defect over the
normal form (A = diag, B = Y diag Y*).  Imports the exact evaluators of census.py.

usage: python3 lbfgs.py m0,m1,m2,m3 k0,k1,k2 which seeds [ps]
"""
import json, math, sys, time
import torch
from census import diag_from, I4, W3, build, relators, reexact, exact_defect


def loss_fn(A, B, which, p):
    n = A.shape[0]
    rs = relators(A, B, which)
    if p == 2:
        return sum(((R - torch.eye(n, dtype=R.dtype)).abs() ** 2).sum() for R in rs.values())
    ss = torch.cat([torch.linalg.svdvals(R - torch.eye(n, dtype=R.dtype)) for R in rs.values()])
    return (ss ** p).sum() ** (2.0 / p)


def optimise(m, k, seed, which, ps=(2, 8, 32, 96), iters=200, rounds=4, K0=None):
    n = sum(m)
    g = torch.Generator().manual_seed(seed)
    if K0 is None:
        K = ((torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g)) / math.sqrt(n)).to(torch.complex128)
    else:
        K = K0.clone()
    K.requires_grad_(True)
    da, db = diag_from(m, I4), diag_from(k, W3)
    for p in ps:
        opt = torch.optim.LBFGS([K], lr=1, max_iter=iters, history_size=50, line_search_fn="strong_wolfe",
                                tolerance_grad=1e-13, tolerance_change=1e-16)

        def closure():
            opt.zero_grad()
            A, B = build(K, da, db)
            loss = loss_fn(A, B, which, p)
            loss.backward()
            return loss

        for _ in range(rounds):
            opt.step(closure)
    A, B = reexact(K, da, db)
    d = exact_defect(A, B, which)
    return max(d.values()), d, K.detach(), A, B


if __name__ == "__main__":
    m = tuple(int(x) for x in sys.argv[1].split(","))
    k = tuple(int(x) for x in sys.argv[2].split(","))
    which = tuple(sys.argv[3].split(","))
    seeds = int(sys.argv[4])
    ps = tuple(int(x) for x in sys.argv[5].split(",")) if len(sys.argv) > 5 else (2, 8, 32, 96)
    best = None
    for s in range(seeds):
        t = time.time()
        D, d, K, A, B = optimise(m, k, s, which, ps)
        print(json.dumps({"m": m, "k": k, "which": which, "seed": s, "D": D, "parts": d,
                          "sec": round(time.time() - t, 1)}), flush=True)
        if best is None or D < best[0]:
            best = (D, s)
    print("BEST", best)
