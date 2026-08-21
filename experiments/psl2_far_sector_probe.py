#!/usr/bin/env python3
"""Far-sector probe: minimize Iwahori defect while REPELLING from the congruence locus.

Goal: probe whether a tuple (x,y,x',y') satisfying the amalgam relations of
PSL_2(Z[1/2]) can have Iwahori defect -> 0 while T = xy stays far from the tested short
odd-order parabolic models.  This is a heuristic screen, not an equivalence with distance
from the full congruence locus: direct sums can have large odd order.  A uniform
tradeoff  defect >= g(farness) > 0  supports flexible HS-stability; defect -> 0 at fixed
farness would be an exotic far-sector solution.

x,y,x',y' keep EXACT torsion orders via spectral-model conjugation.  Loss:
    defect(pi)^2  -  mu * farness(x,y)^2 ,
with farness = min_{m odd <= M} ||(xy)^m - 1||_2  pushed UP (so the optimizer is rewarded
for large farness) but capped so it cannot run away.  We sweep mu and dimension and report
the Pareto frontier (defect vs farness).
"""

from __future__ import annotations

import json
import math
import argparse
import sys
import time

import torch

torch.set_default_dtype(torch.float64)


def hs(A):
    return torch.sqrt(torch.real(torch.trace(A.conj().T @ A)) / A.shape[0])


def unitary(K):
    K = K - K.conj().T
    return torch.linalg.matrix_exp(K)


def defects(x, y, xp, yp):
    T = x @ y
    Tp = xp @ yp
    r1 = T - Tp @ Tp
    eps = x @ y @ y @ x @ y @ x
    epsp = xp @ yp @ xp @ yp @ yp @ xp
    return hs(r1), hs(eps - epsp)


def farness(x, y, M, cap):
    """Soft version of min_{m odd} ||T^m - 1||, capped, differentiable-ish (uses detached argmin)."""
    d = x.shape[0]
    T = x @ y
    I = torch.eye(d, dtype=torch.complex128)
    vals = []
    P = I.clone()
    for m in range(1, M + 1):
        P = P @ T
        if m % 2 == 1:
            vals.append(hs(P - I))
    v = torch.stack(vals)
    soft = -torch.logsumexp(-8.0 * v, dim=0) / 8.0  # smooth min
    return torch.clamp(soft, max=cap)


def balanced_models(d):
    k2 = d // 2
    Dx = torch.diag(torch.tensor([1.0] * k2 + [-1.0] * (d - k2), dtype=torch.complex128))
    w = complex(math.cos(2 * math.pi / 3), math.sin(2 * math.pi / 3))
    k3 = d // 3
    Dy = torch.diag(torch.tensor([1.0] * (d - 2 * k3) + [w] * k3 + [w * w] * k3, dtype=torch.complex128))
    return Dx, Dy


def run(d, mu, restarts, steps, seed, order_factor):
    Dx, Dy = balanced_models(d)
    M = order_factor * d + 1
    cap = 1.2
    torch.manual_seed(seed)
    best = None
    for r in range(restarts):
        params = [torch.randn(d, d, dtype=torch.complex128, requires_grad=True) for _ in range(4)]
        with torch.no_grad():
            for P in params:
                P *= 0.8
        opt = torch.optim.Adam(params, lr=0.02)
        for it in range(steps):
            opt.zero_grad()
            Vs = [unitary(P) for P in params]
            x = Vs[0] @ Dx @ Vs[0].conj().T
            y = Vs[1] @ Dy @ Vs[1].conj().T
            xp = Vs[2] @ Dx @ Vs[2].conj().T
            yp = Vs[3] @ Dy @ Vs[3].conj().T
            a, b = defects(x, y, xp, yp)
            far = farness(x, y, M, cap)
            loss = a * a + b * b - mu * far * far
            loss.backward()
            opt.step()
            if it % 600 == 0 and it > 0:
                for g in opt.param_groups:
                    g["lr"] *= 0.75
        with torch.no_grad():
            Vs = [unitary(P) for P in params]
            x = Vs[0] @ Dx @ Vs[0].conj().T
            y = Vs[1] @ Dy @ Vs[1].conj().T
            xp = Vs[2] @ Dx @ Vs[2].conj().T
            yp = Vs[3] @ Dy @ Vs[3].conj().T
            a, b = defects(x, y, xp, yp)
            # true (hard) farness
            T = x @ y
            I = torch.eye(d, dtype=torch.complex128)
            P = I.clone()
            hard = 9.0
            for m in range(1, M + 1):
                P = P @ T
                if m % 2 == 1:
                    hard = min(hard, float(hs(P - I)))
            dfc = float(max(a, b))
            if best is None or (hard > 0.4 and dfc < best[0]) or (best[1] < 0.4 and hard > best[1]):
                best = (dfc, hard, r)
            rec = {"d": d, "mu": mu, "restart": r, "defect": dfc, "farness": hard}
            print(json.dumps(rec))
            sys.stdout.flush()
    return best


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dimensions", default="12,18,24,30")
    parser.add_argument("--mus", default="0,0.5,1,2")
    parser.add_argument("--restarts", type=int, default=4)
    parser.add_argument("--steps", type=int, default=2500)
    parser.add_argument("--order-factor", type=int, default=4)
    parser.add_argument("--output", default="psl2-far-sector-probe.json")
    args = parser.parse_args()
    t0 = time.time()
    summary = []
    dimensions = tuple(int(x) for x in args.dimensions.split(",") if x)
    mus = tuple(float(x) for x in args.mus.split(",") if x)
    for d in dimensions:
        for mu in mus:
            b = run(d, mu, args.restarts, args.steps,
                    1000 + d + int(10 * mu), args.order_factor)
            summary.append({"d": d, "mu": mu, "best_defect": b[0], "best_farness": b[1]})
            print(f"# d={d} mu={mu} best={b} elapsed={time.time()-t0:.0f}s")
            sys.stdout.flush()
    with open(args.output, "w") as fh:
        json.dump(summary, fh, indent=1)
    print("DONE-SENTINEL")


if __name__ == "__main__":
    main()
