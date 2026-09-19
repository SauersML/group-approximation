"""Planted-control test of search strategies on the full three-relator problem.

The profile m=(0,2,0,2), k=(0,2,2) in U(4) contains the direct sum of two copies
of the certified dimension-two minimiser, so its minimum is <= delta_2 =
0.3491491.  Random-start fixed-profile L-BFGS (lbfgs.optimise, used by
exhaustive.py / locus.py) never reaches it.  This script tests a relator
homotopy: minimise ||r_P - 1||_F^2 + w (||r_1 - 1||_F^2 + ||r_2 - 1||_F^2) with
w increasing from 1e-3 to 1, then the Schatten schedule to p = 256 on all three.

usage: python3 homotopy.py m k seeds out.jsonl [strategy]
strategy: 'homotopy' (default) | 'plain'
"""
import json, math, sys, time
import torch
from census import diag_from, I4, W3, build, relators, reexact, exact_defect

torch.set_default_dtype(torch.float64)


def run(m, k, seed, strategy="homotopy", iters=150, rounds=3):
    n = sum(m)
    g = torch.Generator().manual_seed(seed)
    K = ((torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g)) / math.sqrt(n)).to(torch.complex128)
    K.requires_grad_(True)
    da, db = diag_from(m, I4), diag_from(k, W3)
    eye = torch.eye(n, dtype=torch.complex128)
    stages = []
    if strategy == "homotopy":
        stages += [("w", w) for w in (1e-3, 1e-2, 1e-1, 1.0)]
    stages += [("p", p) for p in (2, 8, 32, 96, 256)]
    for kind, val in stages:
        opt = torch.optim.LBFGS([K], lr=1, max_iter=iters, history_size=50, line_search_fn="strong_wolfe",
                                tolerance_grad=1e-13, tolerance_change=1e-16)

        def closure():
            opt.zero_grad()
            A, B = build(K, da, db)
            rs = relators(A, B)
            if kind == "w":
                f = {q: ((R - eye).abs() ** 2).sum() for q, R in rs.items()}
                loss = f["rP"] + val * (f["r1"] + f["r2"])
            elif val == 2:
                loss = sum(((R - eye).abs() ** 2).sum() for R in rs.values())
            else:
                ss = torch.cat([torch.linalg.svdvals(R - eye) for R in rs.values()])
                loss = (ss ** val).sum() ** (2.0 / val)
            loss.backward()
            return loss

        for _ in range(rounds):
            opt.step(closure)
    A, B = reexact(K, da, db)
    d = exact_defect(A, B)
    return max(d.values()), d


if __name__ == "__main__":
    m = tuple(int(x) for x in sys.argv[1].split(","))
    k = tuple(int(x) for x in sys.argv[2].split(","))
    seeds, out = int(sys.argv[3]), sys.argv[4]
    strat = sys.argv[5] if len(sys.argv) > 5 else "homotopy"
    with open(out, "a") as f:
        for s in range(seeds):
            t = time.time()
            D, d = run(m, k, s, strat)
            rec = {"m": m, "k": k, "strategy": strat, "seed": s, "D": D, "parts": d, "sec": round(time.time() - t, 1)}
            f.write(json.dumps(rec) + "\n")
            f.flush()
            print(json.dumps(rec), flush=True)
