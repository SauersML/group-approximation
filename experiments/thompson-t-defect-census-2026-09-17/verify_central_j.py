"""Numerical checks of the central-J inequalities (claim
thompson-t-defect-gap-central-square-locus).  C = BA, J = A^2, eps2 = ||r_2 - 1||,
epsP = ||r_P - 1||, gam = ||J B - B J||.

  (I0) if J = +-1 then r_2 = [C, B] exactly;
  (I1) J = -1:                       5 eps2 + 2 epsP >= 1;
  (I2) J = +1, B != 1:               5 eps2 + 2 epsP >= sqrt 3;
  (I3) any nontrivial exact pair:    5 eps2 + 2 epsP + 30 gam >= 2/3.

Part 1: random exact pairs, n = 1..8, all profiles sampled.
Part 2: adversarial L-BFGS minimisation of each left-hand side (Schatten p=64
surrogate of each operator norm), random starts, n = 2..6; reports the minimum
ratio LHS / bound, which must be >= 1.
Output: out_verify_central_j.json
"""
import json, math, random
import numpy as np
import torch
from census import diag_from, I4, W3, relators

torch.set_default_dtype(torch.float64)


def comm_B(C, B):
    return C @ B @ C.conj().T @ B.conj().T


def quantities(A, B, smooth=None):
    n = A.shape[0]
    eye = torch.eye(n, dtype=torch.complex128)
    rs = relators(A, B)
    J = A @ A
    if smooth is None:
        nrm = lambda M: torch.linalg.matrix_norm(M, ord=2)
    else:
        # + tiny constant: on the J = +-1 loci gam is identically 0 and the p-th root has an infinite gradient at 0
        nrm = lambda M: ((torch.linalg.svdvals(M) ** smooth).sum() + 1e-200) ** (1.0 / smooth)
    return {"e2": nrm(rs["r2"] - eye), "eP": nrm(rs["rP"] - eye), "e1": nrm(rs["r1"] - eye),
            "gam": nrm(J @ B - B @ J), "J+1": nrm(J + eye), "J-1": nrm(J - eye), "B-1": nrm(B - eye),
            "A-1": nrm(A - eye), "rel_I0": nrm(rs["r2"] - comm_B(B @ A, B))}


def rand_pair(m, k, g):
    n = sum(m)
    K = (torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g)).to(torch.complex128)
    Q, _ = torch.linalg.qr(K)
    return torch.diag(diag_from(m, I4)), Q @ torch.diag(diag_from(k, W3)) @ Q.conj().T


def rand_comp(n, parts, rng):
    cuts = sorted(rng.randint(0, n) for _ in range(parts - 1))
    return tuple(b - a for a, b in zip([0] + cuts, cuts + [n]))


def part1(trials=20000, seed=1):
    rng = random.Random(seed)
    g = torch.Generator().manual_seed(seed)
    worst = {"I0": 0.0, "I1": 9.0, "I2": 9.0, "I3": 9.0}
    counts = {"I1": 0, "I2": 0, "I3": 0}
    for _ in range(trials):
        n = rng.randint(1, 8)
        loc = rng.random()
        if loc < 0.3:
            a = rng.randint(0, n)
            m = (0, a, 0, n - a)          # J = -1
        elif loc < 0.5:
            a = rng.randint(0, n)
            m = (a, 0, n - a, 0)          # J = +1
        else:
            m = rand_comp(n, 4, rng)
        k = rand_comp(n, 3, rng)
        if m[0] == n and k[0] == n:
            continue
        A, B = rand_pair(m, k, g)
        q = {kk: float(v) for kk, v in quantities(A, B).items()}
        L = 5 * q["e2"] + 2 * q["eP"]
        if q["J+1"] < 1e-9:
            worst["I0"] = max(worst["I0"], q["rel_I0"])
            worst["I1"] = min(worst["I1"], L / 1.0)
            counts["I1"] += 1
        if q["J-1"] < 1e-9:
            worst["I0"] = max(worst["I0"], q["rel_I0"])
            if q["B-1"] > 1e-9:
                worst["I2"] = min(worst["I2"], L / math.sqrt(3))
                counts["I2"] += 1
        worst["I3"] = min(worst["I3"], (L + 30 * q["gam"]) / (2.0 / 3.0))
        counts["I3"] += 1
    return {"worst_ratio": worst, "counts": counts}


def part2(which, n, m, k, seed, p=64, iters=200, rounds=3):
    g = torch.Generator().manual_seed(seed)
    K = ((torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g)) / math.sqrt(n)).to(torch.complex128)
    K.requires_grad_(True)
    da, db = diag_from(m, I4), diag_from(k, W3)

    def build():
        Y = torch.matrix_exp(K - K.conj().T)
        return torch.diag(da), Y @ torch.diag(db) @ Y.conj().T

    def lhs(q):
        base = 5 * q["e2"] + 2 * q["eP"]
        return base + 30 * q["gam"] if which == "I3" else base

    opt = torch.optim.LBFGS([K], lr=1, max_iter=iters, history_size=50, line_search_fn="strong_wolfe",
                            tolerance_grad=1e-13, tolerance_change=1e-16)

    def closure():
        opt.zero_grad()
        A, B = build()
        loss = lhs(quantities(A, B, smooth=p))
        loss.backward()
        return loss

    for _ in range(rounds):
        opt.step(closure)
    with torch.no_grad():
        A, B = build()
        Q, _ = torch.linalg.qr(torch.matrix_exp(K - K.conj().T))
        B = Q @ torch.diag(db) @ Q.conj().T
        q = {kk: float(v) for kk, v in quantities(A, B).items()}
    bound = {"I1": 1.0, "I2": math.sqrt(3), "I3": 2.0 / 3.0}[which]
    return lhs(q) / bound, q


if __name__ == "__main__":
    import sys
    # usage: python3 verify_central_j.py [trials nmax seeds iters]
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    nseeds = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 200
    out = {"params": {"trials": trials, "nmax": nmax, "seeds": nseeds, "iters": iters},
           "part1": part1(trials)}
    print(out["part1"], flush=True)
    rng = random.Random(7)
    res = {"I1": [], "I2": [], "I3": []}
    for which in ("I1", "I2", "I3"):
        for n in range(2, nmax + 1):
            for s in range(nseeds):
                if which == "I1":
                    a = rng.randint(1, n - 1)
                    m = (0, a, 0, n - a)
                elif which == "I2":
                    a = rng.randint(0, n)
                    m = (a, 0, n - a, 0)
                else:
                    m = rand_comp(n, 4, rng)
                k = rand_comp(n, 3, rng)
                if k[0] == n:
                    k = (n - 1, 1, 0)
                try:
                    ratio, q = part2(which, n, m, k, s, iters=iters)
                except Exception as e:  # record and continue; a failed run proves nothing either way
                    print(which, n, m, k, s, "ERROR", repr(e)[:80], flush=True)
                    continue
                res[which].append({"n": n, "m": m, "k": k, "seed": s, "ratio": ratio,
                                   "q": {kk: q[kk] for kk in ("e1", "e2", "eP", "gam")}})
                print(which, n, m, k, s, round(ratio, 4), flush=True)
    out["part2_min_ratio"] = {w: min((r["ratio"] for r in v), default=None) for w, v in res.items()}
    out["part2_runs"] = {w: len(v) for w, v in res.items()}
    out["part2"] = res
    json.dump(out, open("out_verify_central_j.json", "w"), indent=1)
    print("MIN RATIOS", out["part2_min_ratio"])
