"""Riemannian census of operator-norm defect for exact Z/4 * Z/3 pairs.

Pairs: A^4 = B^3 = 1 exactly, with prescribed spectral multiplicities.
B is fixed diagonal; A = U D_A U^*, U in U(n) is the optimisation variable.

Defect (Lochak--Schneps relators, see research/thompson-t-lochak-schneps-presentation.md):
  X = B A B,  J = A^2,  W = A^2 B^2 A^2,  W^{-1} = A^2 B A^2
  r1 = [X, J X J],  r2 = [X, W X W^{-1}],  rP = (B A)^5,   [g,h] = g h g^-1 h^-1
  D(A,B) = max_r ||rho(r) - 1||_op.

Smooth surrogate: (1/beta) log sum_r tr exp(beta G_r), G_r = (rho(r)-1)^*(rho(r)-1),
annealed in beta; it tends to max_r lambda_max(G_r) = D^2.
All reported defects are recomputed exactly by SVD in float64 at the end.
"""
import math
import torch

torch.set_default_dtype(torch.float64)
torch.set_num_threads(1)  # small matrices: run independent processes in parallel instead
CD = torch.complex128
OMEGA = complex(math.cos(2 * math.pi / 3), math.sin(2 * math.pi / 3))
A_EIG = [1, 1j, -1, -1j]
B_EIG = [1, OMEGA, OMEGA.conjugate()]


def diag_from_mult(eigs, mult):
    vals = []
    for e, m in zip(eigs, mult):
        vals += [e] * m
    return torch.tensor(vals, dtype=CD)


def relators(A, B):
    n = A.shape[0]
    Ai = A.conj().T
    Bi = B.conj().T
    X = B @ A @ B
    Xi = Bi @ Ai @ Bi
    J = A @ A
    Y = J @ X @ J
    Yi = J @ Xi @ J
    W = J @ B @ B @ J
    Wi = J @ B @ J
    Z = W @ X @ Wi
    Zi = W @ Xi @ Wi
    r1 = X @ Y @ Xi @ Yi
    r2 = X @ Z @ Xi @ Zi
    BA = B @ A
    rP = BA @ BA @ BA @ BA @ BA
    return [r1, r2, rP]


def exact_defects(A, B):
    n = A.shape[0]
    I = torch.eye(n, dtype=CD)
    with torch.no_grad():
        return [float(torch.linalg.matrix_norm(r - I, ord=2)) for r in relators(A, B)]


def pair_from_U(U, dA, dB):
    A = U @ torch.diag(dA) @ U.conj().T
    B = torch.diag(dB)
    return A, B


def random_unitary(n, gen):
    Z = torch.randn(n, n, generator=gen) + 1j * torch.randn(n, n, generator=gen)
    Q, R = torch.linalg.qr(Z.to(CD))
    d = torch.diagonal(R)
    return Q * (d / d.abs())


def optimise(multA, multB, seed=0, steps=3000, lr=0.03, beta0=4.0, beta1=600.0, U0=None,
             absorb_every=50, monotone=False):
    """Adam on the Lie algebra with periodic absorption.

    monotone=False: original (non-monotone) scheme; the start is not evaluated.
    monotone=True : the start is evaluated and kept as incumbent; at every absorption a
                    step block that raises the exact defect D is rejected (U reverts to the
                    incumbent) and lr is halved, so the returned D never exceeds D(U0).
    """
    n = sum(multA)
    assert n == sum(multB)
    gen = torch.Generator().manual_seed(seed)
    dA = diag_from_mult(A_EIG, multA)
    dB = diag_from_mult(B_EIG, multB)
    I = torch.eye(n, dtype=CD)
    U = random_unitary(n, gen) if U0 is None else U0.clone()
    K = torch.zeros(n, n, dtype=CD, requires_grad=True)
    opt = torch.optim.Adam([K], lr=lr)
    best = (float('inf'), None)
    if monotone:
        best = (max(exact_defects(*pair_from_U(U, dA, dB))), U.clone())
    for t in range(steps):
        beta = beta0 * (beta1 / beta0) ** (t / max(1, steps - 1))
        S = K - K.conj().T
        Ut = U @ torch.linalg.matrix_exp(S)
        A, B = pair_from_U(Ut, dA, dB)
        terms = []
        for r in relators(A, B):
            E = r - I
            G = E.conj().T @ E
            G = 0.5 * (G + G.conj().T)
            ev = torch.linalg.eigvalsh(G)
            terms.append(ev)
        ev = torch.cat(terms)
        loss = torch.logsumexp(beta * ev, 0) / beta
        opt.zero_grad()
        loss.backward()
        opt.step()
        if (t + 1) % absorb_every == 0 or t == steps - 1:
            with torch.no_grad():
                S = K - K.conj().T
                U = U @ torch.linalg.matrix_exp(S)
                # re-orthonormalise against drift
                Q, R = torch.linalg.qr(U)
                d = torch.diagonal(R)
                U = Q * (d / d.abs())
                K.zero_()
            A, B = pair_from_U(U, dA, dB)
            D = max(exact_defects(A, B))
            if D < best[0]:
                best = (D, U.clone())
            elif monotone:
                U = best[1].clone()
                lr = max(lr * 0.5, 1e-5)
            opt = torch.optim.Adam([K], lr=lr)
    return best


def spectra_balanced(n12, a=0.0):
    """Multiplicities closest to the T-line fractions of the spectral-balance lemma."""
    n = 12 * n12
    fa = [(1 + 3 * a) / 4] + [(1 - a) / 4] * 3
    fb = [(1 + 2 * a) / 3] + [(1 - a) / 3] * 2

    def rnd(fr):
        m = [int(math.floor(f * n)) for f in fr]
        while sum(m) < n:
            i = max(range(len(fr)), key=lambda j: fr[j] * n - m[j])
            m[i] += 1
        return m
    return rnd(fa), rnd(fb)
