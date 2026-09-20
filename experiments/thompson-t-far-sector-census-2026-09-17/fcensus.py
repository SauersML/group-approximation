"""Far-sector census of D_12 on honest representations of Delta(4,3,5) in U(n), n = 7..12.

Delta = <a, b | a^4, b^3, (ba)^5>,  X = bab,  J = a^2,
  r1 = [X, J X J],  r2 = [X, J b^2 J X J b J]   (Lochak--Schneps words, as in
  experiments/thompson-t-triangle-rep-census-2026-09-17/census.py).
D_12 = max(||r1 - 1||, ||r2 - 1||),  eta = ||[A^2, B] - 1||  (group commutator).

A = U diag(i^alpha) U*,  B = W diag(w^beta) W*  with the eigenvalue type fixed, so A^4 = B^3 = 1
exactly.  Batched Adam on  mu ||(BA)^5 - 1||_F^2 + softmax_t(e1, e2),  mu increasing, where e_i is
the top eigenvalue of (r_i - 1)^*(r_i - 1).  Survivors are projected exactly onto (BA)^5 = 1 by
Levenberg--Marquardt (census.Problem), and every reported number is evaluated on that honest point.

Two start modes:
  random : Haar-ish random U, W.
  seed   : U, W diagonalising a given honest pair (A0, B0) (e.g. a direct sum of lower-dimensional
           minimisers), times exp(i s H) with H random and s the given perturbation size.

Usage:
  python3 fcensus.py random n alpha beta batch seed steps
  python3 fcensus.py seed   file.npz batch seed steps scale
"""
import os
import sys
import numpy as np
import torch
from scipy.optimize import least_squares

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'thompson-t-triangle-rep-census-2026-09-17'))
import census  # noqa: E402

torch.set_default_dtype(torch.float64)
torch.set_num_threads(1)


def herm_batch(x):
    up = torch.triu(x, 1)
    lo = torch.tril(x, -1)
    return (torch.complex(up + up.transpose(1, 2), lo - lo.transpose(1, 2))
            + torch.diag_embed(torch.diagonal(x, dim1=1, dim2=2)).to(torch.complex128))


def eta(A, B):
    J = A @ A
    return census.opdef(J @ B @ J.conj().T @ B.conj().T)


def type_of(A, B):
    """Eigenvalue exponents of A (mu_4), B (mu_3), BA (mu_5)."""
    ea = np.sort(np.round(np.angle(np.linalg.eigvals(A)) / (np.pi / 2)).astype(int) % 4)
    eb = np.sort(np.round(np.angle(np.linalg.eigvals(B)) / (2 * np.pi / 3)).astype(int) % 3)
    ec = np.sort(np.round(np.angle(np.linalg.eigvals(B @ A)) / (2 * np.pi / 5)).astype(int) % 5)
    return ''.join(map(str, ea)), ''.join(map(str, eb)), ''.join(map(str, ec))


def diagonaliser(M, roots):
    """Unitary V and exponent list with M = V diag(roots[e]) V*, for normal M of finite order."""
    w, V = np.linalg.eig(M)
    e = np.array([int(np.argmin(np.abs(roots - x))) for x in w])
    order = np.argsort(e, kind='stable')
    e, V = e[order], V[:, order]
    # re-orthonormalise inside each eigenspace
    Q = np.zeros_like(V)
    for k in set(e.tolist()):
        idx = np.where(e == k)[0]
        q, _ = np.linalg.qr(V[:, idx])
        Q[:, idx] = q
    return Q, e


def optimise(n, alpha, beta, U0s, W0s, steps, lr=0.02, keep=12):
    """U0s, W0s: (batch, n, n) complex starting frames.  Returns honest results sorted by D_12."""
    batch = U0s.shape[0]
    Da = torch.diag(torch.tensor(1j ** np.array(alpha), dtype=torch.complex128))
    Db = torch.diag(torch.tensor(np.exp(2j * np.pi * np.array(beta) / 3), dtype=torch.complex128))
    U0 = torch.tensor(U0s)
    W0 = torch.tensor(W0s)
    xa = torch.zeros(batch, n, n, requires_grad=True)
    xb = torch.zeros(batch, n, n, requires_grad=True)
    I = torch.eye(n, dtype=torch.complex128)
    opt = torch.optim.Adam([xa, xb], lr=lr)
    ct = lambda M: M.conj().transpose(1, 2)

    def mats():
        U = U0 @ torch.matrix_exp(1j * herm_batch(xa))
        W = W0 @ torch.matrix_exp(1j * herm_batch(xb))
        return U, W, U @ Da @ ct(U), W @ Db @ ct(W)

    def terms(A, B):
        J = A @ A
        X = B @ A @ B
        Y1 = J @ X @ J
        Y2 = J @ B @ B @ J @ X @ J @ B @ J
        r1 = X @ Y1 @ ct(X) @ ct(Y1)
        r2 = X @ Y2 @ ct(X) @ ct(Y2)
        C = B @ A
        C5 = C @ C @ C @ C @ C
        pen = ((C5 - I).abs() ** 2).sum((1, 2))
        e1 = torch.linalg.eigvalsh(ct(r1 - I) @ (r1 - I))[:, -1]
        e2 = torch.linalg.eigvalsh(ct(r2 - I) @ (r2 - I))[:, -1]
        return pen, e1, e2

    mus = [1.0, 10.0, 100.0, 1e3, 1e4]
    per = max(1, steps // len(mus))
    for mu in mus:
        for _ in range(per):
            opt.zero_grad()
            U, W, A, B = mats()
            pen, e1, e2 = terms(A, B)
            t = 0.02
            obj = t * torch.logsumexp(torch.stack([e1, e2]) / t, 0)
            (mu * pen + obj).sum().backward()
            opt.step()
    with torch.no_grad():
        U, W, A, B = mats()
        pen, e1, e2 = terms(A, B)
        score = torch.maximum(e1, e2).clamp(min=0).sqrt() + 10 * pen.sqrt()
    prob = census.Problem(n, alpha, beta)
    out = []
    for k in torch.argsort(score).tolist()[:keep]:
        Uk, Wk = U[k].numpy(), W[k].numpy()
        sol = least_squares(prob.resid, np.zeros(2 * n * n), args=(Uk, Wk, 1.0, 0), method='lm',
                            xtol=1e-15, ftol=1e-15, gtol=1e-15)
        Af, Bf = prob.mats(sol.x, Uk, Wk)
        r1, r2, C5 = census.words(Af, Bf)
        res = np.linalg.norm(C5 - np.eye(n), 2)
        if res < 1e-10:
            d1, d2 = census.opdef(r1), census.opdef(r2)
            out.append(dict(D=max(d1, d2), d1=d1, d2=d2, res=res, eta=eta(Af, Bf),
                            comm=census.irreducible(Af, Bf), A=Af, B=Bf))
    out.sort(key=lambda r: r['D'])
    return out


def rand_frames(batch, n, rng):
    return np.stack([census.rand_unitary(n, rng) for _ in range(batch)])


def report(tag, n, a, b, res, save):
    if not res:
        print(tag, n, a, b, 'no-genuine-candidate', flush=True)
        return
    irr = [r for r in res if r['comm'] == 1]
    r = res[0]
    _, _, ec = type_of(r['A'], r['B'])
    line = ('%s %d %s %s genuine=%d best=%.6f d1=%.6f d2=%.6f eta=%.4f comm=%d Ctype=%s res=%.1e'
            % (tag, n, a, b, len(res), r['D'], r['d1'], r['d2'], r['eta'], r['comm'], ec, r['res']))
    if irr:
        ri = irr[0]
        line += ' | irr_best=%.6f irr_eta=%.4f' % (ri['D'], ri['eta'])
    print(line, flush=True)
    np.savez(save, A=r['A'], B=r['B'])


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'random':
        n, a, b = int(sys.argv[2]), sys.argv[3], sys.argv[4]
        batch, seed, steps = int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
        rng = np.random.default_rng(seed)
        F1, F2 = rand_frames(batch, n, rng), rand_frames(batch, n, rng)
        res = optimise(n, [int(c) for c in a], [int(c) for c in b], F1, F2, steps)
        report('R', n, a, b, res, os.path.join(HERE, 'fbest_n%d_a%s_b%s_s%d.npz' % (n, a, b, seed)))
    elif mode == 'seed':
        f = np.load(sys.argv[2])
        batch, seed, steps, scale = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), float(sys.argv[6])
        A0, B0 = f['A'], f['B']
        n = A0.shape[0]
        Ua, ea = diagonaliser(A0, 1j ** np.arange(4))
        Wb, eb = diagonaliser(B0, np.exp(2j * np.pi * np.arange(3) / 3))
        rng = np.random.default_rng(seed)
        F1, F2 = [], []
        for k in range(batch):
            s = 0.0 if k == 0 else scale
            H1 = census.herm(rng.normal(size=n * n), n)
            H2 = census.herm(rng.normal(size=n * n), n)
            F1.append(Ua @ census.expm(1j * s * H1))
            F2.append(Wb @ census.expm(1j * s * H2))
        res = optimise(n, list(ea), list(eb), np.stack(F1), np.stack(F2), steps, lr=0.005)
        a, b = ''.join(map(str, ea)), ''.join(map(str, eb))
        tag = 'S[%s,%.2f]' % (os.path.basename(sys.argv[2]), scale)
        report(tag, n, a, b, res, os.path.join(HERE, 'sbest_n%d_a%s_b%s_%s.npz' % (n, a, b, os.path.basename(sys.argv[2]).replace('.npz', ''))))
