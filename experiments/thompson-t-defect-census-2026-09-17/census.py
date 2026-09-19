"""Numerical census of the operator-norm defect gap of Thompson's T.

Setting (thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes):
  exact pairs (A, B) in U(n), A^4 = B^3 = 1, and
  D(A,B) = max(||r_1 - 1||, ||r_2 - 1||, ||r_P - 1||)   (operator norm),
  r_1 = [X, J X J],  r_2 = [X, W X W^-1],  r_P = (BA)^5,
  X = BAB, J = A^2, W = A^2 B^2 A^2  (so W^-1 = A^2 B A^2).
Words are evaluated left to right as matrix products; by the inversion
symmetry (A,B) -> (A*,B*) the set of defect values over all spectral
profiles does not depend on this convention.

Normal form: A = diag of 4th roots with multiplicities m = (m0..m3),
B = Y diag(cube roots, multiplicities k = (k0,k1,k2)) Y*, Y in U(n).
Y = exp(K - K^H) for a free complex K.  We minimise a smooth surrogate
(Schatten-p norm over the three relators, p increasing) and report the
exact operator-norm defect of the final exact pair.

Every reported value is an honest UPPER bound on delta_n: the final pair
is re-orthonormalised (QR) so A^4 = B^3 = 1 to machine precision, and D is
recomputed by SVD.
"""
import json, math, sys, time
import numpy as np
import torch

torch.set_default_dtype(torch.float64)
I4 = [complex(math.cos(math.pi * j / 2), math.sin(math.pi * j / 2)) for j in range(4)]
W3 = [complex(math.cos(2 * math.pi * j / 3), math.sin(2 * math.pi * j / 3)) for j in range(3)]


def diag_from(mults, roots):
    vals = []
    for r, m in zip(roots, mults):
        vals += [r] * m
    return torch.tensor(vals, dtype=torch.complex128)


def relators(A, B, which=("r1", "r2", "rP")):
    Ai = A.conj().T
    Bi = B.conj().T
    X = B @ A @ B
    Xi = X.conj().T
    J = A @ A
    out = {}
    if "r1" in which:
        Y = J @ X @ J
        out["r1"] = X @ Y @ Xi @ Y.conj().T
    if "r2" in which:
        W = J @ B @ B @ J
        Y = W @ X @ W.conj().T
        out["r2"] = X @ Y @ Xi @ Y.conj().T
    if "rP" in which:
        C = B @ A
        C2 = C @ C
        out["rP"] = C2 @ C2 @ C
    return out


def build(K, da, db):
    Y = torch.matrix_exp(K - K.conj().T)
    A = torch.diag(da)
    B = Y @ torch.diag(db) @ Y.conj().T
    return A, B


def schatten(M, p):
    n = M.shape[0]
    E = M - torch.eye(n, dtype=M.dtype)
    s = torch.linalg.svdvals(E)
    return s


def surrogate(A, B, p, which):
    rs = relators(A, B, which)
    ss = torch.cat([schatten(R, p) for R in rs.values()])
    m = ss.max().detach()
    return m * ((ss / m) ** p).sum() ** (1.0 / p)


def exact_defect(Anp, Bnp, which=("r1", "r2", "rP")):
    A = torch.tensor(Anp)
    B = torch.tensor(Bnp)
    rs = relators(A, B, which)
    n = A.shape[0]
    return {k: float(torch.linalg.matrix_norm(R - torch.eye(n, dtype=R.dtype), ord=2)) for k, R in rs.items()}


def reexact(K, da, db):
    with torch.no_grad():
        Y = torch.matrix_exp(K - K.conj().T)
        Q, R = torch.linalg.qr(Y)
        Q = Q @ torch.diag(torch.diagonal(R) / torch.diagonal(R).abs())
        A = torch.diag(da)
        B = Q @ torch.diag(db) @ Q.conj().T
    return A.numpy(), B.numpy()


def run(m, k, seed, which=("r1", "r2", "rP"), steps=(400, 400, 400, 600), ps=(2, 8, 32, 128), lr=0.03, scale=1.0):
    n = sum(m)
    assert n == sum(k)
    g = torch.Generator().manual_seed(seed)
    K = (scale * (torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g)) / math.sqrt(n)).to(torch.complex128)
    K.requires_grad_(True)
    da, db = diag_from(m, I4), diag_from(k, W3)
    opt = torch.optim.Adam([K], lr=lr)
    for p, st in zip(ps, steps):
        for _ in range(st):
            opt.zero_grad()
            A, B = build(K, da, db)
            loss = surrogate(A, B, p, which)
            loss.backward()
            opt.step()
    Anp, Bnp = reexact(K, da, db)
    d = exact_defect(Anp, Bnp, which)
    return max(d.values()), d, Anp, Bnp


if __name__ == "__main__":
    m = tuple(int(x) for x in sys.argv[1].split(","))
    k = tuple(int(x) for x in sys.argv[2].split(","))
    seeds = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    which = tuple(sys.argv[4].split(",")) if len(sys.argv) > 4 else ("r1", "r2", "rP")
    best = None
    for s in range(seeds):
        t = time.time()
        D, d, A, B = run(m, k, s, which)
        print(json.dumps({"m": m, "k": k, "seed": s, "D": D, "parts": d, "sec": round(time.time() - t, 1)}), flush=True)
        if best is None or D < best[0]:
            best = (D, s)
    print("BEST", best)
