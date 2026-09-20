"""Operator-norm twisted Iwahori matching for the Deligne covers of SL_2(Z[1/2]).

Problem (see research/sl2-half-triple-cover-mf-iff-twisted-iwahori-opnorm-matching.md).  For c = e^{i theta} put
gamma = e^{-i theta/6}.  Unknowns: two exact unitary representations (s, r), (S, R) of PSL_2(Z) = C_2 * C_3 on C^n,
i.e. s^2 = S^2 = 1 and r^3 = R^3 = 1.  With T = s r and L = s r^{-1} (images of [[1,1],[0,1]] and [[1,0],[1,1]]):

    delta(theta) = max( || S R - gamma (s r)^2 || , || s r^{-1} - gamma^{-1} (S R^{-1})^2 || )     (operator norm)

delta_n(theta) = min over all such data in dimension n.  The node proves: W_3 = G~/<z^3> is MF iff
inf_n delta_n(theta) = 0 for theta = pi/3 or theta = 2 pi/3; theta = pi t (mod pi) is the block of central character
z -> e^{2 pi i t}.  Controls: theta = 0 (trivial rep, n = 1) and theta = pi (SL_2(F_3), n = 2) are exactly solvable.

Method: relaxed phases (penalized towards the exact spectra), then snapped to exact spectra and polished with
Schatten-p surrogates p = 2 -> 256; the reported number is the exact operator norm of the snapped, exact data.
Run: python3 match.py --n 1 2 3 --theta 0.3333 --restarts 8     (theta given in units of pi)
"""
import argparse, math, time
import numpy as np
import torch

torch.set_default_dtype(torch.float64)
CD = torch.complex128
W3 = complex(math.cos(2 * math.pi / 3), math.sin(2 * math.pi / 3))


def unitary(H):
    K = (H - H.conj().transpose(-1, -2)) / 2
    return torch.linalg.matrix_exp(K)


def op(U, ph):
    return U @ torch.diag(ph) @ U.conj().T


def logmass(D, p):
    """sum_i sigma_i^p = tr((D^* D)^(p/2)) for p a power of two, by repeated squaring (sigma <= 2, p <= 256);
    avoids eigh backward, which is singular at repeated singular values."""
    M = D.conj().T @ D
    k = p // 2
    while k > 1:
        M = M @ M
        k //= 2
    return torch.real(torch.trace(M))


def defects(s, r, S, R, gamma):
    I = torch.eye(s.shape[0], dtype=CD)
    rinv = r.conj().T
    Rinv = R.conj().T
    T_A = s @ r
    L_B = S @ Rinv
    DT = S @ R - gamma * (T_A @ T_A)
    DU = s @ rinv - (1 / gamma) * (L_B @ L_B)
    return DT, DU


def opnorm(D):
    A = D.detach().numpy()
    return float(np.linalg.norm(A, 2)) if np.all(np.isfinite(A)) else 9.0


def solve(n, theta, seed, steps=600):
    g = torch.Generator().manual_seed(seed)
    gamma = complex(math.cos(-theta / 6), math.sin(-theta / 6))
    Hs = [torch.randn(n, n, dtype=CD, generator=g) * 1.5 for _ in range(4)]
    phis = [torch.rand(n, generator=g) * 2 * math.pi for _ in range(4)]
    for t in Hs + phis:
        t.requires_grad_(True)
    orders = [2, 3, 2, 3]

    def build(ph_exact=None):
        out = []
        for k in range(4):
            U = unitary(Hs[k])
            ph = torch.exp(1j * phis[k]) if ph_exact is None else ph_exact[k]
            out.append(op(U, ph))
        return out

    # stage 1: relaxed spectra, HS then p = 8, with growing penalty
    opt = torch.optim.Adam(Hs + phis, lr=0.05)
    for it in range(steps):
        w = 0.05 + 5.0 * it / steps
        p = 2 if it < steps // 2 else 8
        s, r, S, R = build()
        DT, DU = defects(s, r, S, R, gamma)
        pen = sum(torch.mean(1 - torch.cos(orders[k] * phis[k])) for k in range(4))
        loss = torch.log(logmass(DT, p) + logmass(DU, p) + 1e-300) / p + w * pen
        opt.zero_grad(); loss.backward(); opt.step()
    # snap spectra
    ph_exact = []
    for k in range(4):
        q = 2 * math.pi / orders[k]
        a = torch.round(phis[k].detach() / q) * q
        ph_exact.append(torch.exp(1j * a).to(CD))
    for t in phis:
        t.requires_grad_(False)
    opt = torch.optim.Adam(Hs, lr=0.02)
    best = 9.0
    for p in (8, 32, 128, 256):
        for it in range(steps // 2):
            s, r, S, R = build(ph_exact)
            DT, DU = defects(s, r, S, R, gamma)
            loss = torch.log(logmass(DT, p) + logmass(DU, p) + 1e-300) / p
            opt.zero_grad(); loss.backward(); opt.step()
        with torch.no_grad():
            s, r, S, R = build(ph_exact)
            DT, DU = defects(s, r, S, R, gamma)
            best = min(best, max(opnorm(DT), opnorm(DU)))
    mult = [tuple(int(v) for v in np.bincount(np.round(np.angle(ph.numpy()) / (2 * math.pi / orders[k])).astype(int)
                                               % orders[k], minlength=orders[k])) for k, ph in enumerate(ph_exact)]
    return best, mult


def det_patterns(n, theta):
    """All exact spectral patterns (mult of s, r, S, R) with the determinant (trace-log) cost
    cost = max(|arg e^{i tau_T}|, |arg e^{i tau_U}|), where
    e^{i tau_T} = e^{i n theta/6} det S det R det r, e^{i tau_U} = e^{-i n theta/6} det s / (det R det r).
    Any data in the pattern has delta >= 2 sin(cost / (2 n)).  Returns (min cost, list of minimal patterns)."""
    s_p = [(n - a, a) for a in range(n + 1)]
    r_p = [(n - b - c, b, c) for b in range(n + 1) for c in range(n + 1 - b)]
    out = []
    for ps in s_p:
        for pr in r_p:
            for pS in s_p:
                for pR in r_p:
                    ds, dS = (-1) ** ps[1], (-1) ** pS[1]
                    rho = W3 ** (pr[1] + 2 * pr[2])
                    P = W3 ** (pR[1] + 2 * pR[2])
                    eT = complex(math.cos(n * theta / 6), math.sin(n * theta / 6)) * dS * P * rho
                    eU = complex(math.cos(-n * theta / 6), math.sin(-n * theta / 6)) * ds / (P * rho)
                    cost = max(abs(math.atan2(eT.imag, eT.real)), abs(math.atan2(eU.imag, eU.real)))
                    out.append((round(cost, 9), (ps, pr, pS, pR)))
    m = min(c for c, _ in out)
    return m, [p for c, p in out if c == m]


def spectrum(pat, order):
    return torch.tensor([complex(math.cos(2 * math.pi * k / order), math.sin(2 * math.pi * k / order))
                         for k, m in enumerate(pat) for _ in range(m)], dtype=CD)


def solve_exact(n, theta, pat, seed, steps=400):
    """Exact spectra from the start (no snapping); optimise the four unitaries only."""
    g = torch.Generator().manual_seed(seed)
    gamma = complex(math.cos(-theta / 6), math.sin(-theta / 6))
    orders = [2, 3, 2, 3]
    ph = [spectrum(pat[k], orders[k]) for k in range(4)]
    Hs = [(torch.randn(n, n, dtype=CD, generator=g) * 1.5).requires_grad_(True) for _ in range(4)]
    opt = torch.optim.Adam(Hs, lr=0.05)
    # Adam moves ~lr per step, so decay lr geometrically 0.05 -> 5e-5 or it stalls at defect ~ lr
    sched = torch.optim.lr_scheduler.ExponentialLR(opt, gamma=(1e-3) ** (1.0 / (5 * steps)))
    best = 9.0
    for p in (2, 8, 32, 128, 256):
        for it in range(steps):
            sched.step() if it or p > 2 else None
            s, r, S, R = [op(unitary(Hs[k]), ph[k]) for k in range(4)]
            DT, DU = defects(s, r, S, R, gamma)
            loss = torch.log(logmass(DT, p) + logmass(DU, p) + 1e-300) / p
            opt.zero_grad(); loss.backward(); opt.step()
        with torch.no_grad():
            s, r, S, R = [op(unitary(Hs[k]), ph[k]) for k in range(4)]
            DT, DU = defects(s, r, S, R, gamma)
            best = min(best, max(opnorm(DT), opnorm(DU)))
    # L-BFGS finish on the p = 256 surrogate (second-order convergence where Adam stalls)
    lb = torch.optim.LBFGS(Hs, lr=1, max_iter=steps, line_search_fn="strong_wolfe", tolerance_grad=1e-14,
                           tolerance_change=1e-16, history_size=50)
    def closure():
        lb.zero_grad()
        s, r, S, R = [op(unitary(Hs[k]), ph[k]) for k in range(4)]
        DT, DU = defects(s, r, S, R, gamma)
        loss = torch.log(logmass(DT, 256) + logmass(DU, 256) + 1e-300) / 256
        loss.backward()
        return loss
    try:
        lb.step(closure)
    except RuntimeError:
        pass
    with torch.no_grad():
        s, r, S, R = [op(unitary(Hs[k]), ph[k]) for k in range(4)]
        DT, DU = defects(s, r, S, R, gamma)
        best = min(best, max(opnorm(DT), opnorm(DU)))
    return best


def windings(s, r, S, R, theta):
    """Integer windings (w_T, w_U): tau_T = sum of the phases of (S R)(gamma (s r)^2)^-1 in (-pi, pi) equals
    n theta/6 + (pi/3) w_T; tau_U (phases of (s r^-1)(gamma^-1 (S R^-1)^2)^-1) equals -n theta/6 + (pi/3) w_U.
    Locally constant while delta < 2, so descent never changes them."""
    n = s.shape[0]
    g = complex(math.cos(-theta / 6), math.sin(-theta / 6))
    A = (S @ R) @ np.linalg.inv(g * (s @ r) @ (s @ r))
    B = (s @ np.linalg.inv(r)) @ np.linalg.inv((1 / g) * (S @ np.linalg.inv(R)) @ (S @ np.linalg.inv(R)))
    tT = float(np.sum(np.angle(np.linalg.eigvals(A))))
    tU = float(np.sum(np.angle(np.linalg.eigvals(B))))
    return round((tT - n * theta / 6) * 3 / math.pi, 6), round((tU + n * theta / 6) * 3 / math.pi, 6)


def seed_blocks(tokens):
    """Block-diagonal exact seed.  Tokens: F3 = the 2-dim SL_2(F_3) theta = pi solution (control_pi.py);
    S = scalar theta = 0 solution s = S = 1, r = w, R = w^2 (at theta = pi/3 it is the optimum 2 sin(pi/36));
    Ep / Op = even (theta = 0) / odd (theta = pi) part of the SL_2(F_p) permutation rep, dim (p^2-1)/2.
    At theta = pi/3 each theta = pi dimension carries phase -pi/9 and each theta = 0 dimension +pi/18 in tau_T, so the
    determinant bound of the seed's winding sector vanishes iff dim(theta=0 part) = 2 dim(theta=pi part)."""
    import control_pi as cp
    from scipy.linalg import block_diag
    blocks = []
    for t in tokens:
        if t == "F3":
            blocks.append((cp.s, cp.r, cp.S, cp.R))
        elif t == "S":
            blocks.append((np.eye(1), W3 * np.eye(1), np.eye(1), W3 ** 2 * np.eye(1)))
        else:
            ev, od = perm_blocks(int(t[1:]))
            blocks.append(tuple(ev if t[0] == "E" else od))
    return [block_diag(*[blk[k] for blk in blocks]).astype(complex) for k in range(4)]


def perm_blocks(p):
    """Exact solutions from the permutation rep of SL_2(F_p) (p odd) on F_p^2 minus 0, pulled back to
    SL_2(Z[1/2]).  c = x^2 = -I acts by v -> -v; its +1 part is an exact theta = 0 solution (alpha = beta = 1) and
    its -1 part an exact theta = pi solution (alpha = i, beta = e^{i pi/3}).  Returns (even, odd) lists [s, r, S, R]."""
    inv2 = pow(2, -1, p)
    gens = {"x": ((0, p - 1), (1, 0)), "y": ((0, p - 1), (1, 1)),
            "X": ((0, (-2) % p), (inv2, 0)), "Y": ((0, (-2) % p), (inv2, 1))}
    vecs = [(a, b) for a in range(p) for b in range(p) if (a, b) != (0, 0)]
    idx = {v: i for i, v in enumerate(vecs)}
    N = len(vecs)
    P = {}
    for k, M in gens.items():
        A = np.zeros((N, N))
        for v in vecs:
            w = ((M[0][0] * v[0] + M[0][1] * v[1]) % p, (M[1][0] * v[0] + M[1][1] * v[1]) % p)
            A[idx[w], idx[v]] = 1
        P[k] = A
    reps = [v for v in vecs if idx[v] < idx[((-v[0]) % p, (-v[1]) % p)]]
    E = np.zeros((N, len(reps))); O = np.zeros((N, len(reps)))
    for j, v in enumerate(reps):
        m = idx[((-v[0]) % p, (-v[1]) % p)]
        E[idx[v], j] = E[m, j] = 1 / math.sqrt(2)
        O[idx[v], j] = 1 / math.sqrt(2); O[m, j] = -1 / math.sqrt(2)
    al_e, be_e = 1.0, 1.0
    al_o, be_o = 1j, complex(math.cos(math.pi / 3), math.sin(math.pi / 3))
    even = [E.T @ P[k] @ E / (al_e if k in "xX" else be_e) for k in "xyXY"]
    odd = [O.T @ P[k] @ O / (al_o if k in "xX" else be_o) for k in "xyXY"]
    return [m.astype(complex) for m in even], [m.astype(complex) for m in odd]


def solve_seeded(mats, theta, seed, noise=0.3, steps=400):
    """Optimise s = V s0 V^*, etc. from exact seed data (spectra exact throughout)."""
    g = torch.Generator().manual_seed(seed)
    gamma = complex(math.cos(-theta / 6), math.sin(-theta / 6))
    n = mats[0].shape[0]
    M0 = [torch.tensor(m, dtype=CD) for m in mats]
    Hs = [(torch.randn(n, n, dtype=CD, generator=g) * noise).requires_grad_(True) for _ in range(4)]
    def build():
        out = []
        for k in range(4):
            V = unitary(Hs[k])
            out.append(V @ M0[k] @ V.conj().T)
        return out
    opt = torch.optim.Adam(Hs, lr=0.03)
    sched = torch.optim.lr_scheduler.ExponentialLR(opt, gamma=(1e-2) ** (1.0 / (4 * steps)))
    best, bestm = 9.0, None
    for p in (8, 32, 128, 256):
        for it in range(steps):
            s, r, S, R = build()
            DT, DU = defects(s, r, S, R, gamma)
            loss = torch.log(logmass(DT, p) + logmass(DU, p) + 1e-300) / p
            opt.zero_grad(); loss.backward(); opt.step(); sched.step()
        with torch.no_grad():
            s, r, S, R = build()
            DT, DU = defects(s, r, S, R, gamma)
            d = max(opnorm(DT), opnorm(DU))
            if d < best:
                best, bestm = d, [m.numpy().copy() for m in (s, r, S, R)]
    return best, bestm


if __name__ == "__main__" and "--seeded" in __import__("sys").argv:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seeded", action="store_true")
    ap.add_argument("--blocks", type=str, action="append", required=True, help='e.g. "F3 S S S S"')
    ap.add_argument("--theta", type=float, default=1 / 3)
    ap.add_argument("--noise", type=float, nargs="+", default=[0.0, 0.1, 0.3, 1.0])
    ap.add_argument("--restarts", type=int, default=2)
    ap.add_argument("--steps", type=int, default=300)
    a = ap.parse_args()
    th = a.theta * math.pi
    for spec in a.blocks:
        mats = seed_blocks(spec.split())
        n = mats[0].shape[0]
        t0 = time.time()
        res = []
        for nz in a.noise:
            for sd in range(a.restarts):
                d, m = solve_seeded(mats, th, sd, nz, a.steps)
                res.append((d, nz, windings(*m, th)))
        best = min(res, key=lambda z: z[0])
        g = complex(math.cos(-th / 6), math.sin(-th / 6))
        seed_d = max(np.linalg.norm(mats[2] @ mats[3] - g * np.linalg.matrix_power(mats[0] @ mats[1], 2), 2),
                     np.linalg.norm(mats[0] @ np.linalg.inv(mats[1]) - (1 / g) * np.linalg.matrix_power(
                         mats[2] @ np.linalg.inv(mats[3]), 2), 2))
        print(f"theta={a.theta:.4f}pi blocks=[{spec}] n={n} seed_delta={seed_d:.5f} seed_w={windings(*mats, th)} "
              f"best_delta={best[0]:.5f} noise={best[1]} w={best[2]} all={[round(z[0], 4) for z in res]} "
              f"secs={time.time()-t0:.0f}", flush=True)
    raise SystemExit(0)

if __name__ == "__main__" and "--exact" in __import__("sys").argv:
    ap = argparse.ArgumentParser()
    ap.add_argument("--exact", action="store_true")
    ap.add_argument("--n", type=int, nargs="+", default=[1, 2, 3])
    ap.add_argument("--theta", type=float, nargs="+", default=[1 / 3])
    ap.add_argument("--restarts", type=int, default=8)
    ap.add_argument("--steps", type=int, default=400)
    a = ap.parse_args()
    import random
    for th in a.theta:
        for n in a.n:
            t0 = time.time()
            cost, pats = det_patterns(n, th * math.pi)
            lb = 2 * math.sin(cost / (2 * n))
            rng = random.Random(0)
            res = []
            for seed in range(a.restarts):
                pat = rng.choice(pats)
                res.append((solve_exact(n, th * math.pi, pat, seed, a.steps), pat))
            best = min(res, key=lambda z: z[0])
            print(f"theta={th:.4f}pi n={n:2d} det_lb={lb:.5f} npat={len(pats)} best_delta={best[0]:.5f} "
                  f"median={np.median([z[0] for z in res]):.5f} pat={best[1]} secs={time.time()-t0:.0f}", flush=True)
    raise SystemExit(0)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, nargs="+", default=[1, 2, 3])
    ap.add_argument("--theta", type=float, nargs="+", default=[1 / 3])
    ap.add_argument("--restarts", type=int, default=8)
    ap.add_argument("--steps", type=int, default=600)
    a = ap.parse_args()
    for th in a.theta:
        for n in a.n:
            t0 = time.time()
            res = [solve(n, th * math.pi, seed, a.steps) for seed in range(a.restarts)]
            best = min(res, key=lambda z: z[0])
            print(f"theta={th:.4f}pi n={n:2d} best_delta={best[0]:.5f} median={np.median([z[0] for z in res]):.5f} "
                  f"mult(s,r,S,R)={best[1]} secs={time.time()-t0:.0f}", flush=True)
