"""Far-sector census of exact Delta(4,3,5) representations.

Minimize D12 = max(||rho(r1)-1||, ||rho(r2)-1||) over exact unitary reps
rho of Delta(4,3,5) = <a,b | a^4, b^3, (ba)^5> with prescribed eigenvalue
multiplicity types (mA, mB, mC) for A = rho(a), B = rho(b), C = BA.
r1 = [bab, a^2 bab a^2], r2 = [bab, a^2b^2a^2 bab a^2ba^2] (Lochak-Schneps).

Parametrization: A = diag (4th roots), B = Y B0 Y*, C = Z C0 Z*; the relation
BA = C is imposed by a penalty mu*||BA - C||_F^2 pushed to machine precision.
Reported values are exact operator norms at a point with residual < 1e-9.
Usage: python3 census.py n [restarts] [maxtypes] [seed]
"""
import sys, math, json, itertools, time
import torch

torch.set_default_dtype(torch.float64)
CD = torch.complex128


def rootdiag(k, m):
    vals = []
    for j, mj in enumerate(m):
        vals += [complex(math.cos(2 * math.pi * j / k), math.sin(2 * math.pi * j / k))] * mj
    return torch.tensor(vals, dtype=CD)


def comps(n, k):
    for c in itertools.combinations(range(n + k - 1), k - 1):
        prev, out = -1, []
        for x in c:
            out.append(x - prev - 1)
            prev = x
        out.append(n + k - 1 - prev - 1)
        yield tuple(out)


def det_ok(m, k):
    return sum(j * mj for j, mj in enumerate(m)) % k == 0


def moduli_dim(n, mA, mB, mC):
    s = lambda m: n * n - sum(x * x for x in m)
    return s(mA) + s(mB) + s(mC) - 2 * (n * n - 1)


def imbalance(m, n):
    k = len(m)
    return max(m) - min(m)


def types(n, maxtypes):
    out = []
    for mA in comps(n, 4):
        if not det_ok(mA, 4):
            continue
        for mB in comps(n, 3):
            if not det_ok(mB, 3):
                continue
            for mC in comps(n, 5):
                if not det_ok(mC, 5):
                    continue
                d = moduli_dim(n, mA, mB, mC)
                if d < 0:
                    continue
                score = imbalance(mA, n) + imbalance(mB, n) + imbalance(mC, n)
                out.append((score, -d, mA, mB, mC))
    out.sort()
    return [(o[2], o[3], o[4], -o[1]) for o in out[:maxtypes]]


def skewexp(Pr):
    P = torch.complex(Pr[0], Pr[1])
    S = (P - P.conj().T) / 2
    return torch.linalg.matrix_exp(S)


def build(a, b0, c0, Yb, Zb, PY, PZ):
    Y = Yb @ skewexp(PY)
    Z = Zb @ skewexp(PZ)
    A = torch.diag(a)
    B = Y @ torch.diag(b0) @ Y.conj().T
    C = Z @ torch.diag(c0) @ Z.conj().T
    return A, B, C, Y, Z


def relators(A, B):
    A2 = A @ A
    X = B @ A @ B
    Xh = X.conj().T
    UXU = A2 @ X @ A2
    R1 = X @ UXU @ Xh @ UXU.conj().T
    W = A2 @ B.conj().T @ A2
    WXW = W @ X @ W.conj().T
    R2 = X @ WXW @ Xh @ WXW.conj().T
    return R1, R2


def opdef(R):
    n = R.shape[0]
    I = torch.eye(n, dtype=CD)
    return torch.linalg.matrix_norm(R - I, ord=2).real


def surrogate(R, p=5):
    n = R.shape[0]
    I = torch.eye(n, dtype=CD)
    M = 2 * I - R - R.conj().T
    M = (M + M.conj().T) / 2
    for _ in range(p):
        M = M @ M
    t = torch.trace(M).real.clamp_min(1e-300)
    return t ** (1.0 / (2 * 2 ** p))


def commutant_dim(A, B, tol=1e-7):
    n = A.shape[0]
    I = torch.eye(n, dtype=CD)
    At, Bt = A.T.contiguous(), B.T.contiguous()
    LA = torch.kron(I, A.contiguous()) - torch.kron(At, I)
    LB = torch.kron(I, B.contiguous()) - torch.kron(Bt, I)
    s = torch.linalg.svdvals(torch.cat([LA, LB], 0))
    return int((s < tol).sum())


def run(n, mA, mB, mC, seed, iters=(60, 60, 60, 80)):
    g = torch.Generator().manual_seed(seed)
    a, b0, c0 = rootdiag(4, mA), rootdiag(3, mB), rootdiag(5, mC)

    def haar():
        Mr = torch.randn(n, n, generator=g) + 1j * torch.randn(n, n, generator=g)
        Q, R = torch.linalg.qr(Mr.to(CD))
        return Q

    Yb, Zb = haar(), haar()
    PY = torch.zeros(2, n, n, requires_grad=True)
    PZ = torch.zeros(2, n, n, requires_grad=True)
    hist = []
    for stage, mu in enumerate([1.0, 10.0, 100.0, 1e3, 1e4, 1e5, 1e6]):
        w = 1.0
        opt = torch.optim.LBFGS([PY, PZ], lr=1, max_iter=iters[min(stage, 3)],
                                line_search_fn="strong_wolfe", history_size=30)

        def closure():
            opt.zero_grad()
            A, B, C, _, _ = build(a, b0, c0, Yb, Zb, PY, PZ)
            R1, R2 = relators(A, B)
            f1, f2 = surrogate(R1), surrogate(R2)
            d = (f1 ** 8 + f2 ** 8) ** 0.125
            res = torch.linalg.matrix_norm(B @ A - C) ** 2
            L = w * d + mu * res
            L.backward()
            return L

        opt.step(closure)
        with torch.no_grad():
            A, B, C, Y, Z = build(a, b0, c0, Yb, Zb, PY, PZ)
            Yb, Zb = Y.clone(), Z.clone()
            PY.zero_()
            PZ.zero_()
    # final projection onto the relation BA = C only
    opt = torch.optim.LBFGS([PY, PZ], lr=1, max_iter=400, tolerance_grad=1e-15,
                            tolerance_change=1e-18, line_search_fn="strong_wolfe")

    def closure2():
        opt.zero_grad()
        A, B, C, _, _ = build(a, b0, c0, Yb, Zb, PY, PZ)
        res = torch.linalg.matrix_norm(B @ A - C) ** 2
        res.backward()
        return res

    opt.step(closure2)
    with torch.no_grad():
        A, B, C, Y, Z = build(a, b0, c0, Yb, Zb, PY, PZ)
        res = float(torch.linalg.matrix_norm(B @ A - C).real)
        R1, R2 = relators(A, B)
        d1, d2 = float(opdef(R1)), float(opdef(R2))
        A2 = A @ A
        eta = float(torch.linalg.matrix_norm(A2 @ B - B @ A2, ord=2).real)
        cd = commutant_dim(A, B)
    return dict(n=n, mA=mA, mB=mB, mC=mC, seed=seed, res=res, d1=d1, d2=d2,
                D12=max(d1, d2), eta=eta, commutant=cd)


if __name__ == "__main__":
    n = int(sys.argv[1])
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    maxtypes = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    seed0 = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    torch.set_num_threads(1)
    out = []
    for (mA, mB, mC, d) in types(n, maxtypes):
        for r in range(restarts):
            t0 = time.time()
            rec = run(n, mA, mB, mC, seed0 + 1000 * r + n)
            rec["moduli_dim"] = d
            rec["sec"] = round(time.time() - t0, 1)
            out.append(rec)
            print(json.dumps(rec), flush=True)
