#!/usr/bin/env python3
"""True operator-norm minimax polishing of Higman four-tuples.

Hig = < g_0..g_3 | g_i g_(i+1) g_i^-1 = g_(i+1)^2 >,
def(U) = max_i || U_i U_(i+1) U_i^* - U_(i+1)^2 ||_op.

The earlier census (experiments/higman-opnorm-census-2026-09-17) minimised
Schatten-2m surrogates.  Here the nonsmooth max of the top singular values is
minimised directly by a proximal bundle step: collect every singular triple
(sigma,u,v) of every relator within `tau` of the current maximum, compute the
Riemannian gradient of sigma=Re u^* E v in the skew-Hermitian directions
U_j -> U_j exp(X_j), and take the step X=-rho*sum lambda_k G_k where lambda
solves the dual simplex QP
    min_lambda  rho/2 ||sum lambda_k G_k||^2 - sum lambda_k sigma_k.
A step is accepted only if the true max defect decreases.

Usage:
  python3 minimax_polish.py witness [iters]          polish the L=12 witness
  python3 minimax_polish.py rand L starts iters seed  Schatten warm start + polish
  python3 minimax_polish.py check                     finite-difference test
Saved tuples: set SAVE_TUPLE=path.npy.
"""
import os
import sys
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize

HERE = os.path.dirname(os.path.abspath(__file__))
WITNESS = os.path.join(HERE, "..", "higman-opnorm-census-2026-09-17", "tuple_L12_defect031.txt")


def op(M):
    return np.linalg.norm(M, 2)


def skew(Y):
    return (Y - Y.conj().T) / 2


def relator(U, i):
    A, B = U[i], U[(i + 1) % 4]
    return A @ B @ A.conj().T - B @ B


def defects(U):
    return [op(relator(U, i)) for i in range(4)]


def triple_grad(U, i, u, v):
    """Gradient (4 skew matrices) of Re u^* E_i v under U_j -> U_j exp(X_j)."""
    A, B = U[i], U[(i + 1) % 4]
    W = np.outer(v, u.conj())  # v u^*
    G = [np.zeros_like(U[0]) for _ in range(4)]
    Ms = B @ A.conj().T @ W @ A - A.conj().T @ W @ A @ B
    G[i] += skew(Ms.conj().T)
    Mb = A.conj().T @ W @ A @ B - B @ W @ B - W @ B @ B
    G[(i + 1) % 4] += skew(Mb.conj().T)
    return G


def active(U, tau, kmax=4):
    trip = []
    for i in range(4):
        E = relator(U, i)
        Us, s, Vh = np.linalg.svd(E)
        for k in range(min(kmax, len(s))):
            trip.append((s[k], i, Us[:, k], Vh[k].conj()))
    smax = max(t[0] for t in trip)
    return [t for t in trip if t[0] >= smax - tau], smax


def dual_step(sig, Gs, rho):
    n = len(sig)
    Gm = np.array([np.concatenate([np.concatenate([g.real.ravel(), g.imag.ravel()]) for g in G]) for G in Gs])
    Q = Gm @ Gm.T
    f = lambda lam: 0.5 * rho * lam @ Q @ lam - lam @ sig
    df = lambda lam: rho * Q @ lam - sig
    res = minimize(f, np.ones(n) / n, jac=df, method="SLSQP",
                   bounds=[(0, 1)] * n, constraints=[{"type": "eq", "fun": lambda l: l.sum() - 1, "jac": lambda l: np.ones(n)}],
                   options={"maxiter": 200, "ftol": 1e-14})
    lam = np.clip(res.x, 0, None)
    lam /= lam.sum()
    X = [sum(lam[k] * Gs[k][j] for k in range(n)) * (-rho) for j in range(4)]
    return X


def polish(U, iters=500, tau=0.05, rho=0.5, verbose=100, fixed=()):
    U = [u.copy() for u in U]
    d = max(defects(U))
    for it in range(iters):
        trip, smax = active(U, tau)
        sig = np.array([t[0] for t in trip])
        Gs = [triple_grad(U, t[1], t[2], t[3]) for t in trip]
        for G in Gs:
            for j in fixed:
                G[j][:] = 0
        accepted = False
        while rho > 1e-10:
            X = dual_step(sig, Gs, rho)
            Un = [U[j] @ expm(X[j]) for j in range(4)]
            dn = max(defects(Un))
            if dn < d - 1e-12:
                U, d = Un, dn
                rho = min(rho * 1.5, 5.0)
                accepted = True
                break
            rho /= 2
        if not accepted:
            tau /= 2
            rho = 0.5
            if tau < 1e-9:
                break
        if verbose and it % verbose == 0:
            print(f"  it {it}: def={d:.7f} active={len(trip)} rho={rho:.2e} tau={tau:.1e}", flush=True)
    # re-unitarise
    U = [np.linalg.qr(u)[0] @ np.diag(np.diag(np.linalg.qr(u)[1]) / abs(np.diag(np.linalg.qr(u)[1]))) for u in U]
    return U, max(defects(U))


def load_witness():
    R = np.loadtxt(WITNESS)
    L = int(round(np.sqrt(R.shape[1])))
    return list((R[:4] + 1j * R[4:]).reshape(4, L, L))


def haar(L, rng):
    Z = rng.normal(size=(L, L)) + 1j * rng.normal(size=(L, L))
    Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / abs(np.diag(R)))


def report(U, tag):
    L = U[0].shape[0]
    d = defects(U)
    dist = [op(u - np.eye(L)) for u in U]
    comm = [op(U[0] @ U[2] - U[2] @ U[0]), op(U[1] @ U[3] - U[3] @ U[1])]
    print(f"{tag} L={L}: max def={max(d):.7f} defects={[round(x, 6) for x in d]} "
          f"||U_i-1||={[round(x, 4) for x in dist]} opp comm={[round(x, 3) for x in comm]}", flush=True)
    return max(d), min(dist)


def check():
    rng = np.random.default_rng(1)
    L = 5
    U = [haar(L, rng) for _ in range(4)]
    E = relator(U, 1)
    Us, s, Vh = np.linalg.svd(E)
    u, v = Us[:, 0], Vh[0].conj()
    G = triple_grad(U, 1, u, v)
    X = [skew(rng.normal(size=(L, L)) + 1j * rng.normal(size=(L, L))) for _ in range(4)]
    h = 1e-6
    Up = [U[j] @ expm(h * X[j]) for j in range(4)]
    fd = (np.real(u.conj() @ relator(Up, 1) @ v) - np.real(u.conj() @ E @ v)) / h
    an = sum(np.real(np.trace(G[j].conj().T @ X[j])) for j in range(4))
    print("finite difference", fd, "analytic", an)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "check"
    if mode == "check":
        check()
        return
    if mode == "witness":
        iters = int(sys.argv[2]) if len(sys.argv) > 2 else 400
        U = load_witness()
        report(U, "witness before")
        U, d = polish(U, iters)
        report(U, "witness after")
        if os.environ.get("SAVE_TUPLE"):
            np.save(os.environ["SAVE_TUPLE"], np.array(U))
        return
    if mode == "rand":
        L = int(sys.argv[2])
        starts = int(sys.argv[3])
        iters = int(sys.argv[4])
        seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
        rng = np.random.default_rng(seed)
        best = 9
        for s in range(starts):
            U = [haar(L, rng) for _ in range(4)]
            U, d = polish(U, iters, verbose=0)
            dd, mind = report(U, f"start {s}")
            if mind > 1.0 and dd < best:
                best = dd
                if os.environ.get("SAVE_TUPLE"):
                    np.save(os.environ["SAVE_TUPLE"], np.array(U))
        print(f"BEST far (min ||U_i-1||>1) L={L}: {best:.6f}")


if __name__ == "__main__":
    main()
