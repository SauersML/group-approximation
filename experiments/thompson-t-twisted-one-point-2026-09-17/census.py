"""Twisted one-point gap census for Thompson's group T.

mu_n = min over U, V in U(n) with U^4 = -1 and V^3 = 1 exactly of
    max(||(VU)^5 - 1||, ||r_1(U,V) - 1||, ||r_2(U,V) - 1||),
with X = VUV, J = U^2, W = U^2 V^2 U^2, r_1 = [X, J X J^-1], r_2 = [X, W X W^-1].
(||[x,y] - 1|| = ||xy - yx|| for unitaries.)

By thompson-t-pentagon-winding-rigidity-equals-full-radical item 5 (after exactifying U and V by
functional calculus), T is MF iff inf_n mu_n = 0.

The optimizer returns FEASIBLE points, so every number printed is a rigorous UPPER bound on mu_n
(up to floating-point error in evaluating explicit matrices), never a lower bound.

Usage: python3 census.py NMAX [restarts] [iters] [seed] [mode, e.g. 012 or 01 or 02] [nmin]
"""
import itertools
import math
import sys

import numpy as np
import torch

torch.set_default_dtype(torch.float64)
CD = torch.complex128

U_EIG = [np.exp(1j * math.pi * (2 * k + 1) / 4) for k in range(4)]  # odd 8th roots: u^4 = -1
V_EIG = [np.exp(2j * math.pi * j / 3) for j in range(3)]  # cube roots of 1


def words(U, V):
    n = U.shape[-1]
    I = torch.eye(n, dtype=CD)
    X = V @ U @ V
    J = U @ U
    Ji = J.conj().transpose(-1, -2)
    V2 = V @ V
    W = J @ V2 @ J
    Wi = W.conj().transpose(-1, -2)
    VU = V @ U
    P = VU @ VU
    P = P @ P @ VU
    Y1 = J @ X @ Ji
    Y2 = W @ X @ Wi
    out = [P - I, X @ Y1 - Y1 @ X, X @ Y2 - Y2 @ X]
    return [out[i] for i in MODE]


# which words enter the defect: 0 = pentagon (VU)^5, 1 = r_1, 2 = r_2
MODE = (0, 1, 2)


def opnorms(U, V):
    return [torch.linalg.matrix_norm(M, ord=2).item() for M in words(U, V)]


def unitary_from(H):
    A = H - H.conj().transpose(-1, -2)
    return torch.linalg.matrix_exp(A)


def optimize_batch(pairs, restarts, iters, rng, p=8, lr=0.03):
    """Batched over all (U-type, V-type, restart). Returns best value and witness per pair."""
    n = len(pairs[0][0])
    Ue, De = [], []
    for ue, ve in pairs:
        for _ in range(restarts):
            Ue.append(ue)
            De.append(ve)
    B = len(Ue)
    U = torch.diag_embed(torch.tensor(np.array(Ue), dtype=CD))
    D = torch.diag_embed(torch.tensor(np.array(De), dtype=CD))
    scale = rng.uniform(0.1, 2.0, size=(B, 1, 1))
    H0 = (rng.standard_normal((B, n, n)) + 1j * rng.standard_normal((B, n, n))) * scale
    H = torch.tensor(H0, dtype=CD, requires_grad=True)
    opt = torch.optim.Adam([H], lr=lr)
    sched = torch.optim.lr_scheduler.ExponentialLR(opt, gamma=0.001 ** (1.0 / iters))
    for it in range(iters):
        Y = unitary_from(H)
        V = Y @ D @ Y.conj().transpose(-1, -2)
        s = torch.cat([torch.linalg.svdvals(M) for M in words(U, V)], dim=-1)
        loss = ((s ** p).sum(-1) ** (1.0 / p)).sum()
        opt.zero_grad()
        loss.backward()
        opt.step()
        sched.step()
    with torch.no_grad():
        Y = unitary_from(H)
        V = Y @ D @ Y.conj().transpose(-1, -2)
        vals = torch.stack([torch.linalg.matrix_norm(M, ord=2) for M in words(U, V)], -1).max(-1).values
    vals = vals.reshape(len(pairs), restarts)
    idx = vals.argmin(-1)
    Vr = V.reshape(len(pairs), restarts, n, n)
    return [(vals[i, idx[i]].item(), Vr[i, idx[i]]) for i in range(len(pairs))]


def types(eigs, n):
    return list(itertools.combinations_with_replacement(range(len(eigs)), n))


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    global MODE
    if len(sys.argv) > 5:
        MODE = tuple(int(c) for c in sys.argv[5])
    print(f"words in defect: {MODE}  (0=(VU)^5, 1=r_1, 2=r_2)")
    rng = np.random.default_rng(seed)
    mu1 = 2 * math.sin(math.pi / 24)
    print(f"reference mu_1 = 2 sin(pi/24) = {mu1:.6f}")
    nmin = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    for n in range(nmin, nmax + 1):
        pairs, labels = [], []
        for tu in types(U_EIG, n):
            for tv in types(V_EIG, n):
                pairs.append(([U_EIG[k] for k in tu], [V_EIG[k] for k in tv]))
                labels.append((tu, tv))
        if n == 1:
            res = []
            for ue, ve in pairs:
                U = torch.diag(torch.tensor(ue, dtype=CD))
                V = torch.diag(torch.tensor(ve, dtype=CD))
                res.append((max(opnorms(U, V)), V))
        else:
            res = optimize_batch(pairs, restarts, iters, rng)
        order = sorted(range(len(res)), key=lambda i: res[i][0])
        for i in order[:5]:
            print(f"  n={n} {res[i][0]:.6f} U-type {labels[i][0]} V-type {labels[i][1]}")
        best = res[order[0]][0]
        print(f"n={n}: upper bound mu_n <= {best:.6f}  (ratio to mu_1: {best / mu1:.4f})", flush=True)

if __name__ == "__main__":
    main()
