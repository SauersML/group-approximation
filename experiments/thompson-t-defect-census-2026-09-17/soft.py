"""Soft-spectrum search: A = exp(H_A), B = exp(H_B) with free skew-Hermitian H,
penalty lam*(||A^4-1||_F^2 + ||B^3-1||_F^2) with lam increasing, then spectral
rounding of A to 4th roots and B to cube roots (functional calculus), and exact
re-evaluation of D.  The profile is chosen by the optimiser, not fixed.

Optional start: 'dsum2' = direct sum of copies of the certified 2-dim minimiser
(p=(1,3), q=(1,2), t=0.101486) plus trivial characters, perturbed by eps.

usage: python3 soft.py n seeds [start] [eps]
"""
import json, math, sys, time
import numpy as np
import torch
from census import relators

torch.set_default_dtype(torch.float64)


def skew(M):
    return M - M.conj().T


def round_spectrum(U, k):
    w, V = np.linalg.eig(U)
    # unitary normal: use Schur for a stable eigenbasis
    import scipy.linalg as sl
    T, Z = sl.schur(U, output="complex")
    d = np.diag(T)
    ang = np.angle(d)
    j = np.round(ang * k / (2 * np.pi)) % k
    roots = np.exp(2j * np.pi * j / k)
    R = Z @ np.diag(roots) @ Z.conj().T
    return R, np.bincount(j.astype(int), minlength=k)


def exact_D(A, B):
    At, Bt = torch.tensor(A), torch.tensor(B)
    rs = relators(At, Bt)
    n = A.shape[0]
    return {k: float(torch.linalg.matrix_norm(R - torch.eye(n, dtype=R.dtype), ord=2)) for k, R in rs.items()}


def start_dsum2(n):
    t = 0.101486
    c, s = math.cos(t), math.sin(t)
    Y = np.array([[c, -s], [s, c]], dtype=complex)
    a2 = np.diag([1j, -1j])
    w = np.exp(2j * np.pi / 3)
    b2 = Y @ np.diag([w, w * w]) @ Y.conj().T
    A = np.eye(n, dtype=complex)
    B = np.eye(n, dtype=complex)
    for j in range(n // 2):
        A[2 * j:2 * j + 2, 2 * j:2 * j + 2] = a2
        B[2 * j:2 * j + 2, 2 * j:2 * j + 2] = b2
    return A, B


def logm_u(U):
    import scipy.linalg as sl
    T, Z = sl.schur(U, output="complex")
    return Z @ np.diag(1j * np.angle(np.diag(T))) @ Z.conj().T


def run(n, seed, start=None, eps=0.3, lams=(1, 10, 100, 1000), ps=(2, 2, 8, 32), iters=200, rounds=3):
    g = torch.Generator().manual_seed(seed)
    rnd = lambda: (torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g)).to(torch.complex128)
    if start == "dsum2":
        A0, B0 = start_dsum2(n)
        HA = torch.tensor(logm_u(A0)) + eps * skew(rnd()) / math.sqrt(n)
        HB = torch.tensor(logm_u(B0)) + eps * skew(rnd()) / math.sqrt(n)
    else:
        HA = 2.0 * skew(rnd()) / math.sqrt(n)
        HB = 2.0 * skew(rnd()) / math.sqrt(n)
    HA.requires_grad_(True)
    HB.requires_grad_(True)
    eye = torch.eye(n, dtype=torch.complex128)
    for lam, p in zip(lams, ps):
        opt = torch.optim.LBFGS([HA, HB], lr=1, max_iter=iters, history_size=50, line_search_fn="strong_wolfe",
                                tolerance_grad=1e-13, tolerance_change=1e-16)

        def closure():
            opt.zero_grad()
            A = torch.matrix_exp(skew(HA) / 2)
            B = torch.matrix_exp(skew(HB) / 2)
            rs = relators(A, B)
            if p == 2:
                rel = sum(((R - eye).abs() ** 2).sum() for R in rs.values())
            else:
                ss = torch.cat([torch.linalg.svdvals(R - eye) for R in rs.values()])
                rel = (ss ** p).sum() ** (2.0 / p)
            A2 = A @ A
            B2 = B @ B
            pen = ((A2 @ A2 - eye).abs() ** 2).sum() + ((B2 @ B - eye).abs() ** 2).sum()
            # keep the pair away from (1,1): reward distance of A,B from identity
            triv = 1.0 / (((A - eye).abs() ** 2).sum() + ((B - eye).abs() ** 2).sum() + 1e-9)
            loss = rel + lam * pen + 0.1 * triv
            loss.backward()
            return loss

        for _ in range(rounds):
            opt.step(closure)
    with torch.no_grad():
        A = torch.matrix_exp(skew(HA) / 2).numpy()
        B = torch.matrix_exp(skew(HB) / 2).numpy()
    Ar, ma = round_spectrum(A, 4)
    Br, mb = round_spectrum(B, 3)
    d = exact_D(Ar, Br)
    nontriv = bool(ma[0] < n or mb[0] < n)
    return max(d.values()), d, ma.tolist(), mb.tolist(), nontriv, Ar, Br


if __name__ == "__main__":
    n, seeds = int(sys.argv[1]), int(sys.argv[2])
    start = sys.argv[3] if len(sys.argv) > 3 else None
    eps = float(sys.argv[4]) if len(sys.argv) > 4 else 0.3
    best = None
    for s in range(seeds):
        t = time.time()
        D, d, ma, mb, nt, A, B = run(n, s, start, eps)
        print(json.dumps({"n": n, "seed": s, "start": start, "D": D, "parts": d, "m": ma, "k": mb, "nontrivial": nt,
                          "sec": round(time.time() - t, 1)}), flush=True)
        if nt and (best is None or D < best[0]):
            best = (D, s)
            np.save("best_soft_n%d.npy" % n, np.stack([A, B]))
    print("BEST", best)
