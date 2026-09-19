"""Local stability of the dimension-two minimiser under direct sums.

Start at A0 = diag, B0 = block direct sum of `c` copies of the certified 2-dim
minimiser (p=(1,3), q=(1,2), t=0.101486) and a list of one-dimensional
characters (p:q).  Parametrise B = U B0 U*, U = exp(K - K*), A = A0 fixed
(exact: spectra never move), and minimise the Schatten-p surrogate of the
three-relator defect from K = eps * gaussian, p up to 512.  Report the exact
operator-norm D of the result.  Question: does any nearby exact pair in the
same spectral profile beat delta_2 = 0.3491491?

usage: python3 perturb_dsum.py copies "p:q,..."|- eps seeds out.jsonl
"""
import json, math, sys, time
import numpy as np
import torch
from census import relators, exact_defect

torch.set_default_dtype(torch.float64)
T0 = 0.101486
DELTA2 = 0.34914910598516


def start(copies, chars):
    c, s = math.cos(T0), math.sin(T0)
    Y = np.array([[c, -s], [s, c]], dtype=complex)
    w = np.exp(2j * np.pi / 3)
    a2 = np.diag([1j, -1j])
    b2 = Y @ np.diag([w, w * w]) @ Y.conj().T
    n = 2 * copies + len(chars)
    A = np.eye(n, dtype=complex)
    B = np.eye(n, dtype=complex)
    for j in range(copies):
        A[2 * j:2 * j + 2, 2 * j:2 * j + 2] = a2
        B[2 * j:2 * j + 2, 2 * j:2 * j + 2] = b2
    for j, (p, q) in enumerate(chars):
        i = 2 * copies + j
        A[i, i] = 1j ** p
        B[i, i] = w ** q
    return A, B


def run(copies, chars, eps, seed, ps=(8, 32, 96, 256, 512), iters=200, rounds=3):
    A0, B0 = start(copies, chars)
    n = A0.shape[0]
    At, B0t = torch.tensor(A0), torch.tensor(B0)
    g = torch.Generator().manual_seed(seed)
    K = (eps * (torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g))).to(torch.complex128)
    K.requires_grad_(True)
    eye = torch.eye(n, dtype=torch.complex128)

    def build():
        U = torch.matrix_exp(K - K.conj().T)
        return At, U @ B0t @ U.conj().T

    for p in ps:
        opt = torch.optim.LBFGS([K], lr=1, max_iter=iters, history_size=50, line_search_fn="strong_wolfe",
                                tolerance_grad=1e-14, tolerance_change=1e-17)

        def closure():
            opt.zero_grad()
            A, B = build()
            ss = torch.cat([torch.linalg.svdvals(R - eye) for R in relators(A, B).values()])
            loss = (ss ** p).sum() ** (2.0 / p)
            loss.backward()
            return loss

        for _ in range(rounds):
            opt.step(closure)
    with torch.no_grad():
        U = torch.matrix_exp(K - K.conj().T)
        Q, _ = torch.linalg.qr(U)
        B = (Q @ B0t @ Q.conj().T).numpy()
    d = exact_defect(A0, B)
    return max(d.values()), d


if __name__ == "__main__":
    copies = int(sys.argv[1])
    chars = [] if sys.argv[2] == "-" else [tuple(int(t) for t in c.split(":")) for c in sys.argv[2].split(",")]
    eps, seeds, out = float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    A0, B0 = start(copies, chars)
    d0 = exact_defect(A0, B0)
    with open(out, "a") as f:
        for s in range(seeds):
            t = time.time()
            D, d = run(copies, chars, eps, s)
            rec = {"copies": copies, "chars": chars, "eps": eps, "seed": s, "D0": max(d0.values()), "D": D,
                   "parts": d, "beats_delta2": D < DELTA2 - 1e-9, "sec": round(time.time() - t, 1)}
            f.write(json.dumps(rec) + "\n")
            f.flush()
            print(json.dumps(rec), flush=True)
