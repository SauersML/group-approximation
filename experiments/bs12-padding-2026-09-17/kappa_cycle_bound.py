"""Checks for bs12-identity-padding-inert-off-doubling-fixed-point.

Part A (Item 3): for every irreducible exact BS(1,2) packet rho(O,mu) with
O != {1}, kappa = min_v (||Cv-v||^2+||Zv-v||^2)^(1/2) >= 1/L, L=|O|.
Enumerates all squaring cycles of odd n-th roots of unity, odd n <= NMAX,
over a grid of twists mu, and reports the minimal ratio kappa*L.

Part B (Item 1): random gapped instances.  Build an exact packet
rho = sigma (+) (U, 1_k) with sigma b-fixed-point free, conjugate by a unitary
W0 close to 1, read off (A,B) as the compression to the first block and
measure eps; then run the removal of Item 1 and check the bound
eps(1+16/gamma).
"""
import numpy as np

rng = np.random.default_rng(0)
NMAX = 257
MUS = np.exp(2j * np.pi * np.linspace(0, 1, 9, endpoint=False))


def cycles(n):
    seen, out = set(), []
    for a in range(1, n):
        if a in seen:
            continue
        orb, x = [], a
        while x not in orb:
            orb.append(x)
            x = (2 * x) % n
        if x != a:
            continue
        seen.update(orb)
        out.append(orb)
    return out


def irrep(n, orb, mu):
    L = len(orb)
    C = np.zeros((L, L), complex)
    for j in range(L - 1):
        C[j + 1, j] = 1
    C[0, L - 1] = mu
    # C e_j = e_(j+1) and C Z C^* = Z^2 force lambda_(j+1)^2 = lambda_j,
    # so the eigenvalues run along the squaring cycle backwards.
    Z = np.diag(np.exp(2j * np.pi * np.array(orb[::-1]) / n))
    return C, Z


def part_a():
    worst = (np.inf, None)
    for n in range(3, NMAX + 1, 2):
        for orb in cycles(n):
            L = len(orb)
            for mu in MUS:
                C, Z = irrep(n, orb, mu)
                assert np.allclose(C @ Z @ C.conj().T, Z @ Z)
                S = np.vstack([C - np.eye(L), Z - np.eye(L)])
                r = np.linalg.svd(S, compute_uv=False).min() * L
                if r < worst[0]:
                    worst = (r, (n, L, orb[:4], round(float(np.angle(mu)), 3)))
    print("Part A: min kappa*L =", worst)


def haar(m):
    X = rng.normal(size=(m, m)) + 1j * rng.normal(size=(m, m))
    Q, R = np.linalg.qr(X)
    return Q * (np.diag(R) / abs(np.diag(R)))


def expm_skew(H):
    w, V = np.linalg.eigh(H)
    return V @ np.diag(np.exp(1j * w)) @ V.conj().T


def removal_item1(C, Z, n, k, M, N):
    P = np.zeros((n + k, n + k))
    P[n:, n:] = np.eye(k)
    w, V = np.linalg.eig(Z)
    eps = max(np.linalg.norm(C - M, 2), np.linalg.norm(Z - N, 2))
    sel = abs(w - 1) <= eps + 1e-9
    Vs, _ = np.linalg.qr(V[:, sel])
    Pp = Vs @ Vs.conj().T
    assert np.linalg.norm(C @ Pp @ C.conj().T - Pp, 2) < 1e-8
    T = Pp @ P + (np.eye(n + k) - Pp) @ (np.eye(n + k) - P)
    U_, s_, Vh_ = np.linalg.svd(T)
    W = U_ @ Vh_
    C1 = W.conj().T @ C @ W
    Z1 = W.conj().T @ Z @ W
    C0, Z0 = C1[:n, :n], Z1[:n, :n]
    assert np.allclose(C0 @ Z0 @ C0.conj().T, Z0 @ Z0, atol=1e-8)
    return max(np.linalg.norm(C0 - M[:n, :n], 2), np.linalg.norm(Z0 - N[:n, :n], 2))


def part_b(trials=200):
    worst = 0.0
    for _ in range(trials):
        n0 = int(rng.choice([3, 5, 7, 9, 15, 21]))
        cyc = [c for c in cycles(n0)]
        blocks = [irrep(n0, cyc[rng.integers(len(cyc))], np.exp(2j * np.pi * rng.random()))
                  for _ in range(rng.integers(1, 4))]
        Cs = [b[0] for b in blocks]
        Zs = [b[1] for b in blocks]
        n = sum(c.shape[0] for c in Cs)
        k = int(rng.integers(1, 4))
        C = np.zeros((n + k, n + k), complex)
        Z = np.zeros((n + k, n + k), complex)
        o = 0
        for c, z in zip(Cs, Zs):
            m = c.shape[0]
            C[o:o + m, o:o + m] = c
            Z[o:o + m, o:o + m] = z
            o += m
        C[n:, n:] = haar(k)
        Z[n:, n:] = np.eye(k)
        H = rng.normal(size=(n + k, n + k)) + 1j * rng.normal(size=(n + k, n + k))
        H = (H + H.conj().T) / 2
        H *= 10 ** rng.uniform(-4, -2) / np.linalg.norm(H, 2)
        W0 = expm_skew(H)
        C = W0 @ C @ W0.conj().T
        Z = W0 @ Z @ W0.conj().T
        A, B = C[:n, :n], Z[:n, :n]
        # polar-normalize the compressions to unitaries
        u, _, vh = np.linalg.svd(A)
        A = u @ vh
        u, _, vh = np.linalg.svd(B)
        B = u @ vh
        M = np.zeros_like(C)
        N = np.zeros_like(Z)
        M[:n, :n] = A
        N[:n, :n] = B
        N[n:, n:] = np.eye(k)
        # padding by U on which b is trivial: use the actual corner of C
        u, _, vh = np.linalg.svd(C[n:, n:])
        M[n:, n:] = u @ vh
        gamma = np.min(abs(np.linalg.eigvals(B) - 1))
        eps = max(np.linalg.norm(C - M, 2), np.linalg.norm(Z - N, 2))
        if eps >= gamma / 8:
            continue
        err = removal_item1(C, Z, n, k, M, N)
        ratio = err / (eps * (1 + 16 / gamma))
        worst = max(worst, ratio)
    print("Part B: max err / (eps(1+16/gamma)) =", worst)


if __name__ == "__main__":
    part_a()
    part_b()
