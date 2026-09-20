"""Refine census.py on chosen eigen-types, with p-continuation (8 -> 64), and save explicit witnesses.

Usage: python3 refine.py MODE UTYPE VTYPE [restarts] [iters] [seed] [tag]
  e.g. python3 refine.py 01 0113 0122 64 1500 5 a

U = diag of odd 8th roots with the given indices (exact, U^4 = -1), V = Y D Y* with D the cube roots of
the given indices; Y is re-orthonormalised by QR in numpy before evaluation, so V^3 = 1 holds to machine
precision. Every value printed is the operator-norm max-defect of an explicit feasible pair, hence an
upper bound on mu_n^S for the word set S = MODE (plus a floating-point error of order 1e-14).
Writes witness_<MODE>_<UTYPE>_<VTYPE>_<tag>.npz (U, V) and prints the per-word defects.
"""
import math
import sys

import numpy as np
import torch

import census

mode = tuple(int(c) for c in sys.argv[1])
tu = [int(c) for c in sys.argv[2]]
tv = [int(c) for c in sys.argv[3]]
restarts = int(sys.argv[4]) if len(sys.argv) > 4 else 64
iters = int(sys.argv[5]) if len(sys.argv) > 5 else 1500
seed = int(sys.argv[6]) if len(sys.argv) > 6 else 0
tag = sys.argv[7] if len(sys.argv) > 7 else "a"
census.MODE = mode
n = len(tu)
CD = census.CD
ue = np.array([census.U_EIG[k] for k in tu])
ve = np.array([census.V_EIG[k] for k in tv])
rng = np.random.default_rng(seed)
U = torch.diag_embed(torch.tensor(np.tile(ue, (restarts, 1)), dtype=CD))
D = torch.diag_embed(torch.tensor(np.tile(ve, (restarts, 1)), dtype=CD))
scale = rng.uniform(0.1, 2.0, size=(restarts, 1, 1))
H = torch.tensor((rng.standard_normal((restarts, n, n)) + 1j * rng.standard_normal((restarts, n, n))) * scale,
                 dtype=CD, requires_grad=True)
for p, its, lr in ((8, iters, 0.03), (24, iters // 2, 0.005), (64, iters // 2, 0.001)):
    opt = torch.optim.Adam([H], lr=lr)
    sched = torch.optim.lr_scheduler.ExponentialLR(opt, gamma=0.01 ** (1.0 / its))
    for _ in range(its):
        Y = census.unitary_from(H)
        V = Y @ D @ Y.conj().transpose(-1, -2)
        s = torch.cat([torch.linalg.svdvals(M) for M in census.words(U, V)], dim=-1)
        loss = ((s ** p).sum(-1) ** (1.0 / p)).sum()
        opt.zero_grad()
        loss.backward()
        opt.step()
        sched.step()

with torch.no_grad():
    Y = census.unitary_from(H).numpy()


def defects(Un, Vn):
    I = np.eye(n)
    X = Vn @ Un @ Vn
    J = Un @ Un
    W = J @ Vn @ Vn @ J
    P5 = np.linalg.matrix_power(Vn @ Un, 5)
    Y1 = J @ X @ J.conj().T
    Y2 = W @ X @ W.conj().T
    nr = lambda M: float(np.linalg.norm(M, 2))
    return {"U4+1": nr(np.linalg.matrix_power(Un, 4) + I), "V3-1": nr(np.linalg.matrix_power(Vn, 3) - I),
            "pent": nr(P5 - I), "r1": nr(X @ Y1 - Y1 @ X), "r2": nr(X @ Y2 - Y2 @ X)}


names = ["pent", "r1", "r2"]
best = None
Un = np.diag(ue)
for b in range(restarts):
    Q, R = np.linalg.qr(Y[b])
    Q = Q @ np.diag(np.diag(R) / np.abs(np.diag(R)))
    Vn = Q @ np.diag(ve) @ Q.conj().T
    d = defects(Un, Vn)
    m = max(d[names[i]] for i in mode)
    if best is None or m < best[0]:
        best = (m, Vn, d)
mu1 = 2 * math.sin(math.pi / 24)
m, Vn, d = best
print(f"mode {sys.argv[1]} U-type {tu} V-type {tv}: best max-defect {m:.6f} (ratio to mu_1 {m / mu1:.4f})")
print("  per-word defects of the witness:", {k: round(v, 6) for k, v in d.items()})
np.savez(f"witness_{sys.argv[1]}_{sys.argv[2]}_{sys.argv[3]}_{tag}.npz", U=Un, V=Vn)
