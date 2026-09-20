"""Planted census for delta_n of Thompson's T (Lochak--Schneps presentation) with kappa_P.

Exact pairs: A = diag(i^k), B = U diag(w^j) U^*, U = exp(K - K^*).  A 1-dim block (k,j)
is an exact scalar pair; r1 = r2 = 1 on it and rP = zeta^5, zeta = i^k w^j.
Init: a random direct sum of 1-dim blocks (types sampled), K = eps * noise, then minimise
logsumexp_beta of the three operator-norm defects.  Reports D and 12 kappa_P, where
kappa_P = sum principal arg eig((BA)^5) / 2 pi.

usage: python3 tcensus2.py n trials which steps eps [seed]
"""
import sys, math, random
import torch
torch.set_default_dtype(torch.float64)
CD = torch.complex128

def comm(x, y):
    return x @ y @ x.conj().T @ y.conj().T

def relators(A, B):
    I = torch.eye(A.shape[0], dtype=CD)
    J = A @ A
    X = B @ A @ B
    r1 = comm(X, J @ X @ J)
    W = J @ B @ B @ J
    r2 = comm(X, W @ X @ W.conj().T)
    BA = B @ A
    P = BA @ BA @ BA @ BA @ BA
    return [r1 - I, r2 - I, P - I], P

def make(ks, js, K):
    a = torch.tensor([k * math.pi / 2 for k in ks])
    b = torch.tensor([j * 2 * math.pi / 3 for j in js])
    A = torch.diag(torch.exp(1j * a.to(CD)))
    U = torch.linalg.matrix_exp(K - K.conj().T)
    B = U @ torch.diag(torch.exp(1j * b.to(CD))) @ U.conj().T
    return A, B

def evalpair(A, B, which):
    rs, P = relators(A, B)
    ds = [torch.linalg.matrix_norm(rs[i], ord=2).item() for i in range(3)]
    ev = torch.linalg.eigvals(P)
    k12 = 12 * torch.angle(ev).sum().item() / (2 * math.pi)
    return max(ds[i] for i in which), ds, k12

def run(ks, js, seed, steps, which, eps, lr=0.02):
    n = len(ks)
    g = torch.Generator().manual_seed(seed)
    K = ((torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g)) * eps).to(CD)
    K.requires_grad_(True)
    opt = torch.optim.Adam([K], lr=lr)
    best = None
    for t in range(steps):
        A, B = make(ks, js, K)
        rs, _ = relators(A, B)
        beta = 10.0 + 200.0 * t / steps
        norms = torch.stack([torch.linalg.matrix_norm(rs[i], ord=2) for i in which])
        loss = torch.logsumexp(beta * norms, 0) / beta
        opt.zero_grad(); loss.backward(); opt.step()
        if t % 25 == 0 or t == steps - 1:
            with torch.no_grad():
                A, B = make(ks, js, K)
                D, ds, k12 = evalpair(A, B, which)
                if best is None or D < best[0]:
                    best = (D, ds, k12)
    return best

if __name__ == "__main__":
    n = int(sys.argv[1]); trials = int(sys.argv[2])
    which = tuple(int(c) for c in sys.argv[3]); steps = int(sys.argv[4]); eps = float(sys.argv[5])
    seed0 = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    rnd = random.Random(1000 * n + seed0)
    types = [(k, j) for k in range(4) for j in range(3)] if len(sys.argv) < 8 else [(0, 0), (1, 1), (3, 2)]
    out = []
    for tr in range(trials):
        blocks = [rnd.choice(types) for _ in range(n)]
        if all(b == (0, 0) for b in blocks):
            continue
        blocks.sort()
        ks = [b[0] for b in blocks]; js = [b[1] for b in blocks]
        mA = tuple(ks.count(k) for k in range(4)); mB = tuple(js.count(j) for j in range(3))
        best = run(ks, js, seed0 * 100000 + 1000 * n + tr, steps, which, eps)
        D, ds, k12 = best
        out.append((D, mA, mB, k12))
        print(n, mA, mB, "D=%.5f" % D, "ds=" + ",".join("%.4f" % x for x in ds), "12k=%.4f" % k12, flush=True)
    out.sort()
    print("BEST", n, out[0] if out else None, flush=True)
