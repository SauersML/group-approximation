"""Census: distance from the Fourier-twisted clock pair (A_s, D) to exact BS(1,2) pairs.

A_s = W exp(i s (V+V^*)),  D = diag(w^j),  W e_j = e_(j/2 mod N),  N odd.
Exact pairs with simple N-th-root base spectrum are exactly
    Z = U D U^*,  C = U W diag(e^{i theta}) U^*,  U in U(N), theta in R^N
(because {C : C D C^* = D^2} = W * diagonal unitaries when spec D is simple).
We minimize  max(||C - A_s||, ||Z - D||)  (operator norm) with a Schatten-p
surrogate and L-BFGS, and report the true operator norms of the best point.
Every reported number is an UPPER bound for the distance to exact pairs with
simple N-th-root spectrum (it is a feasible exact pair).

usage: python3 census.py N s [restarts] [p]
"""
import sys, math, torch

torch.set_default_dtype(torch.float64)
import os
SAVE = os.environ.get("CENSUS_SAVE")


def setup(N, s):
    j = torch.arange(N)
    w = torch.exp(2j * math.pi * j / N)
    D = torch.diag(w).to(torch.complex128)
    half = (N + 1) // 2
    W = torch.zeros(N, N, dtype=torch.complex128)
    W[(j * half) % N, j] = 1.0          # W e_j = e_(j/2)
    V = torch.zeros(N, N, dtype=torch.complex128)
    V[(j + 1) % N, j] = 1.0             # V e_j = e_(j+1)
    H = V + V.conj().T
    A = W @ torch.linalg.matrix_exp(1j * s * H)
    assert torch.allclose(W @ D @ W.conj().T, D @ D)
    return A, D, W


def opn(X):
    return torch.linalg.matrix_norm(X, ord=2).item()


def run(N, s, restarts=3, p=24, iters=400, seed=0):
    A, D, W = setup(N, s)
    defect = opn(A @ D @ A.conj().T - D @ D)
    g = torch.Generator().manual_seed(seed)
    best = None
    for r in range(restarts):
        scale = 0.0 if r == 0 else 0.3 / math.sqrt(N)
        Kr = (scale * torch.randn(N, N, generator=g)).requires_grad_()
        Ki = (scale * torch.randn(N, N, generator=g)).requires_grad_()
        th = torch.zeros(N).requires_grad_()
        params = [Kr, Ki, th]

        def build():
            K = torch.complex(Kr, Ki)
            U = torch.linalg.matrix_exp(K - K.conj().T)
            Z = U @ D @ U.conj().T
            C = U @ W @ torch.diag(torch.exp(1j * th)) @ U.conj().T
            return C, Z

        for pp in (p, 2 * p):
            opt = torch.optim.LBFGS(params, lr=1, max_iter=iters,
                                    history_size=50, line_search_fn="strong_wolfe")

            def closure():
                opt.zero_grad()
                C, Z = build()
                ec = torch.linalg.eigvalsh((C - A).conj().T @ (C - A)).clamp_min(0)
                ez = torch.linalg.eigvalsh((Z - D).conj().T @ (Z - D)).clamp_min(0)
                L = (torch.sum(ec ** (pp / 2)) + torch.sum(ez ** (pp / 2))) ** (1 / pp)
                L.backward()
                return L

            opt.step(closure)
        with torch.no_grad():
            C, Z = build()
            K = torch.complex(Kr, Ki)
            U = torch.linalg.matrix_exp(K - K.conj().T)
            dc, dz = opn(C - A), opn(Z - D)
            rel = opn(C @ Z @ C.conj().T - Z @ Z)
        val = max(dc, dz)
        if best is None or val < best[0]:
            best = (val, dc, dz, rel, r)
            best_UZC = (U.detach().numpy(), th.detach().numpy())
    if SAVE:
        import numpy as np
        np.savez(SAVE, U=best_UZC[0], theta=best_UZC[1], N=N, s=s)
    return defect, best


if __name__ == "__main__":
    N = int(sys.argv[1]); s = float(sys.argv[2])
    R = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    p = int(sys.argv[4]) if len(sys.argv) > 4 else 24
    A, D, W = setup(N, s)
    base = opn(A - W)
    defect, (val, dc, dz, rel, r) = run(N, s, R, p)
    print(f"N={N} s={s} defect={defect:.4g} ||A_s-W||={base:.4f} "
          f"best max={val:.4f} (||C-A||={dc:.4f}, ||Z-D||={dz:.4f}, exact rel err={rel:.1e}, restart {r})")
