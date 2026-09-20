"""Batched torch census of gamma_n on honest representations of Delta(4,3,5).

Same words and parametrisation as census.py.  Many random starts are optimised at once with
Adam on  mu * ||(BA)^5 - 1||_F^2 + softmax(||r_1 - 1||^2, ||r_2 - 1||^2),  mu increasing.
The best candidates are then projected exactly onto the variety (BA)^5 = 1 by Levenberg-
Marquardt in census.py, and the reported values are evaluated on those genuine points.

Usage: python3 tcensus.py n alpha beta batch seed [steps]
"""
import sys
import numpy as np
import torch
import census

torch.set_default_dtype(torch.float64)
torch.set_num_threads(1)


def herm_batch(x, n):
    # x: (batch, n, n) real -> Hermitian
    up = torch.triu(x, 1)
    lo = torch.tril(x, -1)
    H = torch.complex(up + up.transpose(1, 2), lo - lo.transpose(1, 2)) + torch.diag_embed(torch.diagonal(x, dim1=1, dim2=2)).to(torch.complex128)
    return H


def run(n, alpha, beta, batch, seed, steps=3000):
    g = torch.Generator().manual_seed(seed)
    Da = torch.diag(torch.tensor(1j ** np.array(alpha), dtype=torch.complex128))
    Db = torch.diag(torch.tensor(np.exp(2j * np.pi * np.array(beta) / 3), dtype=torch.complex128))
    xa = (torch.randn(batch, n, n, generator=g) * 2.0).requires_grad_()
    xb = (torch.randn(batch, n, n, generator=g) * 2.0).requires_grad_()
    I = torch.eye(n, dtype=torch.complex128)
    opt = torch.optim.Adam([xa, xb], lr=0.02)

    def mats():
        U = torch.matrix_exp(1j * herm_batch(xa, n))
        W = torch.matrix_exp(1j * herm_batch(xb, n))
        A = U @ Da @ U.conj().transpose(1, 2)
        B = W @ Db @ W.conj().transpose(1, 2)
        return U, W, A, B

    def loss_terms(A, B):
        J = A @ A
        X = B @ A @ B
        Y1 = J @ X @ J
        Y2 = J @ B @ B @ J @ X @ J @ B @ J
        ct = lambda M: M.conj().transpose(1, 2)
        r1 = X @ Y1 @ ct(X) @ ct(Y1)
        r2 = X @ Y2 @ ct(X) @ ct(Y2)
        C = B @ A
        C5 = C @ C @ C @ C @ C
        pen = ((C5 - I).abs() ** 2).sum((1, 2))
        e1 = torch.linalg.eigvalsh(ct(r1 - I) @ (r1 - I))[:, -1]
        e2 = torch.linalg.eigvalsh(ct(r2 - I) @ (r2 - I))[:, -1]
        return pen, e1, e2

    mus = [1.0, 10.0, 100.0, 1e3, 1e4]
    per = steps // len(mus)
    for mu in mus:
        for s in range(per):
            opt.zero_grad()
            U, W, A, B = mats()
            pen, e1, e2 = loss_terms(A, B)
            t = 0.02
            obj = t * torch.logsumexp(torch.stack([e1, e2]) / t, 0)
            L = (mu * pen + obj).sum()
            L.backward()
            opt.step()
    with torch.no_grad():
        U, W, A, B = mats()
        pen, e1, e2 = loss_terms(A, B)
        score = torch.maximum(e1, e2).sqrt() + 10 * pen.sqrt()
    order = torch.argsort(score).tolist()
    prob = census.Problem(n, alpha, beta)
    results = []
    for k in order[:12]:
        U0 = U[k].numpy()
        W0 = W[k].numpy()
        from scipy.optimize import least_squares
        sol = least_squares(prob.resid, np.zeros(2 * n * n), args=(U0, W0, 1.0, 0), method='lm',
                            xtol=1e-15, ftol=1e-15, gtol=1e-15)
        Af, Bf = prob.mats(sol.x, U0, W0)
        r1, r2, C5 = census.words(Af, Bf)
        res = np.linalg.norm(C5 - np.eye(n), 2)
        if res < 1e-10:
            results.append((max(census.opdef(r1), census.opdef(r2)), census.opdef(r1), census.opdef(r2), res, Af, Bf))
    results.sort(key=lambda r: r[0])
    return results


if __name__ == '__main__':
    n = int(sys.argv[1])
    a, b = sys.argv[2], sys.argv[3]
    batch, seed = int(sys.argv[4]), int(sys.argv[5])
    steps = int(sys.argv[6]) if len(sys.argv) > 6 else 3000
    res = run(n, [int(c) for c in a], [int(c) for c in b], batch, seed, steps)
    if not res:
        print(n, a, b, 'no-genuine-candidate')
    else:
        v, d1, d2, r, Af, Bf = res[0]
        cd = census.irreducible(Af, Bf)
        ce = np.sort(np.round(np.angle(np.linalg.eigvals(Bf @ Af)) / (2 * np.pi) * 5).astype(int) % 5)
        print(n, a, b, 'genuine=%d best=%.6f d1=%.6f d2=%.6f res=%.1e commutant=%d Ctype=%s next=%s'
              % (len(res), v, d1, d2, r, cd, ''.join(map(str, ce)),
                 ','.join('%.4f' % x[0] for x in res[1:5])), flush=True)
        np.savez('tbest_n%d_a%s_b%s.npz' % (n, a, b), A=Af, B=Bf)
