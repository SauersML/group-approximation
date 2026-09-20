"""Improved exact Delta(4,3,5) census: land on the rep variety first, then
descend D12 with a sharpening schedule (Frobenius -> Schatten-2^p -> operator).
Usage: python3 census2.py n restarts maxtypes seed [typefilter]
typefilter: optional 'mA/mB/mC' like 1123/122/11111 to run one type only.
"""
import sys, json, time, math
import torch
from census import (CD, rootdiag, types, build, relators, opdef, commutant_dim,
                    moduli_dim)

torch.set_default_dtype(torch.float64)


def schatten(R, p):
    n = R.shape[0]
    I = torch.eye(n, dtype=CD)
    M = 2 * I - R - R.conj().T
    M = (M + M.conj().T) / 2
    for _ in range(p):
        M = M @ M
    t = torch.trace(M).real.clamp_min(1e-300)
    return t ** (1.0 / (2 * 2 ** p))


def lbfgs(params, fn, iters):
    opt = torch.optim.LBFGS(params, lr=1, max_iter=iters, tolerance_grad=1e-13,
                            tolerance_change=1e-16, line_search_fn="strong_wolfe",
                            history_size=40)

    def closure():
        opt.zero_grad()
        L = fn()
        L.backward()
        return L

    opt.step(closure)


def run(n, mA, mB, mC, seed, sched=((0, 1e2), (2, 1e3), (4, 1e4), (6, 1e5))):
    g = torch.Generator().manual_seed(seed)
    a, b0, c0 = rootdiag(4, mA), rootdiag(3, mB), rootdiag(5, mC)

    def haar():
        M = torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g)
        return torch.linalg.qr(M.to(CD))[0]

    st = {"Yb": haar(), "Zb": haar()}
    PY = torch.zeros(2, n, n, requires_grad=True)
    PZ = torch.zeros(2, n, n, requires_grad=True)

    def rebase():
        with torch.no_grad():
            A, B, C, Y, Z = build(a, b0, c0, st["Yb"], st["Zb"], PY, PZ)
            st["Yb"], st["Zb"] = Y.clone(), Z.clone()
            PY.zero_()
            PZ.zero_()

    def resid():
        A, B, C, _, _ = build(a, b0, c0, st["Yb"], st["Zb"], PY, PZ)
        return torch.linalg.matrix_norm(B @ A - C) ** 2

    lbfgs([PY, PZ], resid, 300)
    rebase()
    for p, mu in sched:
        def obj():
            A, B, C, _, _ = build(a, b0, c0, st["Yb"], st["Zb"], PY, PZ)
            R1, R2 = relators(A, B)
            f1, f2 = schatten(R1, p), schatten(R2, p)
            d = (f1 ** 8 + f2 ** 8) ** 0.125
            return d + mu * torch.linalg.matrix_norm(B @ A - C) ** 2
        for _ in range(2):
            lbfgs([PY, PZ], obj, 150)
            rebase()
    lbfgs([PY, PZ], resid, 400)
    rebase()
    with torch.no_grad():
        A, B, C, Y, Z = build(a, b0, c0, st["Yb"], st["Zb"], PY, PZ)
        res = float(torch.linalg.matrix_norm(B @ A - C).real)
        R1, R2 = relators(A, B)
        d1, d2 = float(opdef(R1)), float(opdef(R2))
        A2 = A @ A
        eta = float(torch.linalg.matrix_norm(A2 @ B - B @ A2, ord=2).real)
        cdim = commutant_dim(A, B)
    return dict(n=n, mA=mA, mB=mB, mC=mC, seed=seed, res=res, d1=d1, d2=d2,
                D12=max(d1, d2), eta=eta, commutant=cdim), (A, B)


if __name__ == "__main__":
    n = int(sys.argv[1])
    restarts = int(sys.argv[2])
    maxtypes = int(sys.argv[3])
    seed0 = int(sys.argv[4])
    filt = sys.argv[5] if len(sys.argv) > 5 else None
    torch.set_num_threads(1)
    best = None
    for (mA, mB, mC, d) in types(n, maxtypes):
        key = "".join(map(str, mA)) + "/" + "".join(map(str, mB)) + "/" + "".join(map(str, mC))
        if filt and key != filt:
            continue
        for r in range(restarts):
            t0 = time.time()
            rec, (A, B) = run(n, mA, mB, mC, seed0 + 7919 * r + 31 * n)
            rec["moduli_dim"] = d
            rec["sec"] = round(time.time() - t0, 1)
            print(json.dumps(rec), flush=True)
            if rec["res"] < 1e-8 and rec["commutant"] == 1 and (best is None or rec["D12"] < best[0]):
                best = (rec["D12"], A, B, rec)
    if best is not None:
        torch.save({"A": best[1], "B": best[2], "rec": best[3]},
                   "best_n%d_s%d.pt" % (n, seed0))
