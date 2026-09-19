#!/usr/bin/env python3
"""Correlated (matrix-product / hidden-Markov) pointed-forest test vectors for ||P|| on Thompson's F.

Model and embedding: research/thompson-f-norm-bound-from-forest-renewal-test-vector-proof.md.
States: (T_0..T_{m-1}; i), trees with n leaves in total.  Moves: pointer right, merge at pointer.

Ansatz (bond dimension q, all matrices entrywise positive):
    x(leaf) = X1,  x((L,R)) = x(L) Phi(|L|,|R|) x(R)
    y(leaf) = Y1,  y((L,R)) = y(L) Gam(|L|,|R|) x(R)
    f(T_0..T_{m-1}; i) = u^T [prod_{j<i} x(T_j) R] y(T_i) R [prod_{j>i} x(T_j) R] v
Trees with more than N leaves get weight 0.  q = 1 is the split-form ansatz of split_ansatz.py.

Kronecker shape sums over trees with s leaves (q^2 x q^2 matrices):
    A_s = sum x(x)x,  Bq_s = sum y(x)y,  X_s = sum x(x)y,  Xp_s = sum y(x)x
    A_n  = sum_{l+r=n} A_l (Phi(x)Phi) A_r,   Bq_n = sum Bq_l (Gam(x)Gam) A_r,
    X_n  = sum X_l (Phi(x)Gam) A_r,           Xp_n = sum Xp_l (Gam(x)Phi) A_r.
With RR = R(x)R:
    D_n   = (u(x)u)^T sum_{l+s+r=n} Z_l [Bq_s RR] Z_r (v(x)v),     Z_m = sum_s Z_{m-s} A_s RR, Z_0 = I
    Num_n = 2 (u(x)u)^T sum Z_l H_j Z_r (v(x)v),
    H_j   = sum_{s+t=j} Xp_s RR X_t RR + sum_{k+l=j, k+l<=N} Bq_k (R(x)Gam(k,l)) A_l RR.
The stationary (n -> infinity) quotient: normalise R so that the Perron root of sum_s A_s RR is 1,
with Perron vectors lam (left), rv (right); then Num/D -> lam^T H rv / lam^T Q rv, H = sum H_j,
Q = sum Bq_s RR.  (Checked against the finite DP in `test`.)
"""
import sys, itertools, random
import torch

torch.set_default_dtype(torch.float64)


def kron(a, b):
    return torch.kron(a, b)


def shape_sums(P, N):
    """P: dict with lPhi, lGam (N+1,N+1,q,q), lX1, lY1, lR (q,q); log-parametrised."""
    Phi, Gam = torch.exp(P['lPhi']), torch.exp(P['lGam'])
    X1, Y1 = torch.exp(P['lX1']), torch.exp(P['lY1'])
    A = [None, kron(X1, X1)]
    Bq = [None, kron(Y1, Y1)]
    X = [None, kron(X1, Y1)]
    Xp = [None, kron(Y1, X1)]
    q = X1.shape[0]

    def bk(a, b):  # batched kron over leading dim
        return (a[:, :, None, :, None] * b[:, None, :, None, :]).reshape(a.shape[0], q * q, q * q)

    for n in range(2, N + 1):
        l = torch.arange(1, n)
        Ph, Ga = Phi[l, n - l], Gam[l, n - l]
        Ar = torch.stack(A[1:n][::-1])
        a = (torch.stack(A[1:n]) @ bk(Ph, Ph) @ Ar).sum(0)
        b = (torch.stack(Bq[1:n]) @ bk(Ga, Ga) @ Ar).sum(0)
        x = (torch.stack(X[1:n]) @ bk(Ph, Ga) @ Ar).sum(0)
        xp = (torch.stack(Xp[1:n]) @ bk(Ga, Ph) @ Ar).sum(0)
        A.append(a); Bq.append(b); X.append(x); Xp.append(xp)
    return A, Bq, X, Xp, Gam


def pieces(P, N, R):
    A, Bq, X, Xp, Gam = shape_sums(P, N)
    RR = kron(R, R)
    As = [None] + [A[s] @ RR for s in range(1, N + 1)]
    Qs = [None] + [Bq[s] @ RR for s in range(1, N + 1)]
    q2 = RR.shape[0]
    Hs = [None] + [torch.zeros(q2, q2) for _ in range(2 * N)]
    for s in range(1, N + 1):
        for t in range(1, N + 1):
            Hs[s + t] = Hs[s + t] + Xp[s] @ RR @ X[t] @ RR
    for k in range(1, N):
        for l in range(1, N - k + 1):
            Hs[k + l] = Hs[k + l] + Bq[k] @ kron(R, Gam[k, l]) @ A[l] @ RR
    return As, Qs, Hs


def finite_ratio(P, N, n, u, v):
    """Exact Num_n / D_n by the matrix renewal DP (float64)."""
    R = torch.exp(P['lR'])
    As, Qs, Hs = pieces(P, N, R)
    uu, vv = kron(u[None, :], u[None, :])[0], kron(v[None, :], v[None, :])[0]
    # left vectors L_m = uu^T Z_m ; right vectors Rv_m = Z_m vv
    Lv = [uu]
    Rv = [vv]
    for m in range(1, n + 1):
        lm = 0; rm = 0
        for s in range(1, min(N, m) + 1):
            lm = lm + Lv[m - s] @ As[s]
            rm = rm + As[s] @ Rv[m - s]
        Lv.append(lm); Rv.append(rm)
    D = 0; Num = 0
    for l in range(0, n):
        for s in range(1, min(N, n - l) + 1):
            D = D + Lv[l] @ Qs[s] @ Rv[n - l - s]
        for j in range(2, min(2 * N, n - l) + 1):
            Num = Num + Lv[l] @ Hs[j] @ Rv[n - l - j]
    return (2 * Num / D), D, 2 * Num


def perron(M, iters=400):
    q2 = M.shape[0]
    r = torch.ones(q2) / q2
    l = torch.ones(q2) / q2
    for _ in range(iters):
        r = M @ r; r = r / r.sum()
        l = l @ M; l = l / l.sum()
    lamb = (l @ M @ r) / (l @ r)
    return lamb, l, r


def stationary_ratio(P, N):
    R0 = torch.exp(P['lR'])
    A, Bq, X, Xp, Gam = shape_sums(P, N)
    M = sum(A[s] for s in range(1, N + 1)) @ kron(R0, R0)
    lamb, _, _ = perron(M)
    R = R0 / torch.sqrt(lamb)
    RR = kron(R, R)
    q = R.shape[0]
    _, l, r = perron(sum(A[1:]) @ RR)
    Q = sum(Bq[1:]) @ RR
    H = sum(Xp[1:]) @ RR @ sum(X[1:]) @ RR
    At = torch.stack(A[1:])          # index l-1
    Bt = torch.stack(Bq[1:])
    for k in range(1, N):
        ls = torch.arange(1, N - k + 1)
        G = Gam[k, ls]              # (N-k, q, q)
        RG = (R[None, :, None, :, None] * G[:, None, :, None, :]).reshape(len(ls), q * q, q * q)
        H = H + (Bt[k - 1] @ RG @ At[ls - 1]).sum(0) @ RR
    return 2 * (l @ H @ r) / (l @ Q @ r)


# ---------------- brute force ----------------
def trees(n):
    if n == 1:
        yield 'o'; return
    for l in range(1, n):
        for L in trees(l):
            for Rt in trees(n - l):
                yield (L, Rt)


def size(T):
    return 1 if T == 'o' else size(T[0]) + size(T[1])


def compositions(n):
    if n == 0:
        yield (); return
    for s in range(1, n + 1):
        for rest in compositions(n - s):
            yield (s,) + rest


def brute(P, N, n, u, v):
    Phi, Gam = torch.exp(P['lPhi']), torch.exp(P['lGam'])
    X1, Y1, R = torch.exp(P['lX1']), torch.exp(P['lY1']), torch.exp(P['lR'])
    q = R.shape[0]

    def xw(T):
        if T == 'o':
            return X1
        if size(T) > N:
            return torch.zeros(q, q)
        return xw(T[0]) @ Phi[size(T[0]), size(T[1])] @ xw(T[1])

    def yw(T):
        if T == 'o':
            return Y1
        if size(T) > N:
            return torch.zeros(q, q)
        return yw(T[0]) @ Gam[size(T[0]), size(T[1])] @ xw(T[1])

    def f(F, i):
        M = u[None, :]
        for j, T in enumerate(F):
            M = M @ (yw(T) if j == i else xw(T)) @ R
        return (M @ v).item()

    states = []
    for comp in compositions(n):
        for F in itertools.product(*[list(trees(s)) for s in comp]):
            for i in range(len(F)):
                states.append((F, i))
    D = sum(f(F, i) ** 2 for F, i in states)
    Num = 0
    for F, i in states:
        if i + 1 < len(F):
            Num += f(F, i) * f(F, i + 1)
            G = F[:i] + ((F[i], F[i + 1]),) + F[i + 2:]
            Num += f(F, i) * f(G, i)
    return 2 * Num / D, D, 2 * Num


def random_params(N, q, scale=0.5, seed=0):
    g = torch.Generator().manual_seed(seed)
    return {'lPhi': scale * torch.randn(N + 1, N + 1, q, q, generator=g) - 1.0,
            'lGam': scale * torch.randn(N + 1, N + 1, q, q, generator=g) - 1.0,
            'lX1': scale * torch.randn(q, q, generator=g) - 0.7,
            'lY1': scale * torch.randn(q, q, generator=g) - 0.7,
            'lR': scale * torch.randn(q, q, generator=g)}


if __name__ == "__main__" and sys.argv[1:2] == ['test']:
    for q in (1, 2):
        for n in range(2, 7):
            P = random_params(4, q, seed=n + 10 * q)
            u = torch.rand(q) + 0.1; v = torch.rand(q) + 0.1
            rb, Db, Nb = brute(P, 4, n, u, v)
            rd, Dd, Nd = finite_ratio(P, 4, n, u, v)
            print(f"q={q} n={n} brute D={Db:.12g} Num={Nb:.12g}  dp D={Dd.item():.12g} "
                  f"Num={Nd.item():.12g}  rel={abs(Db-Dd.item())/Db:.1e},{abs(Nb-Nd.item())/Nb:.1e}")
    P = random_params(6, 2, seed=5)
    u = torch.rand(2) + 0.1; v = torch.rand(2) + 0.1
    st = stationary_ratio(P, 6).item()
    for n in (50, 200, 800):
        # rescale R so the renewal is critical, as in stationary_ratio
        A, _, _, _, _ = shape_sums(P, 6)
        R0 = torch.exp(P['lR'])
        lamb, _, _ = perron(sum(A[1:]) @ kron(R0, R0))
        P2 = dict(P); P2['lR'] = P['lR'] - 0.5 * torch.log(lamb)
        print(f"n={n} finite={finite_ratio(P2, 6, n, u, v)[0].item():.10f} stationary={st:.10f}")
