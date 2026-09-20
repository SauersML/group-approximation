"""Census of gamma_n for honest unitary representations of Delta(4,3,5).

Delta = <a, b | a^4, b^3, (ba)^5>.  T = Delta / <<r1, r2>> with
  X  = b a b,  J = a^2,
  r1 = [X, J X J],
  r2 = [X, J b^2 J X J b J].
gamma_n = min over nontrivial rho: Delta -> U(n) of max_i ||rho(r_i) - 1||.

Parametrisation: A = U diag(alpha) U*, B = W diag(beta) W*, with alpha in mu_4^n and
beta in mu_3^n fixed (the conjugacy-class type).  Then A^4 = B^3 = 1 exactly, and only
(BA)^5 = 1 is imposed, by a penalty that is driven to machine precision at the end.

Usage: python3 census.py n alpha beta runs seed
  alpha: string of exponents k (eigenvalue i^k), e.g. "123"
  beta : string of exponents k (eigenvalue w^k), e.g. "012"
"""
import sys
import numpy as np
from scipy.optimize import least_squares


def expm(M):
    """exp(M) for M = i H with H Hermitian, via eigh (scipy.linalg.expm is slow here)."""
    H = -1j * M
    w, V = np.linalg.eigh((H + H.conj().T) / 2)
    return (V * np.exp(1j * w)) @ V.conj().T


def herm(x, n):
    H = np.zeros((n, n), complex)
    iu = np.triu_indices(n, 1)
    k = len(iu[0])
    H[iu] = x[:k] + 1j * x[k:2 * k]
    H = H + H.conj().T
    H[np.diag_indices(n)] = x[2 * k:2 * k + n]
    return H


def rand_unitary(n, rng):
    Z = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / abs(np.diag(R)))


def words(A, B):
    n = A.shape[0]
    Ai = A.conj().T
    Bi = B.conj().T
    J = A @ A
    X = B @ A @ B
    Xi = X.conj().T
    Y1 = J @ X @ J
    Y2 = J @ B @ B @ J @ X @ J @ B @ J
    r1 = X @ Y1 @ Xi @ Y1.conj().T
    r2 = X @ Y2 @ Xi @ Y2.conj().T
    C = B @ A
    C5 = np.linalg.matrix_power(C, 5)
    return r1, r2, C5


def opdef(M):
    """||M - 1|| for unitary M = 2 sin(theta_max / 2)."""
    return np.linalg.norm(M - np.eye(M.shape[0]), 2)


def angles(M):
    return np.angle(np.linalg.eigvals(M))


class Problem:
    def __init__(self, n, alpha, beta):
        self.n = n
        self.Da = np.diag(1j ** np.array(alpha))
        self.Db = np.diag(np.exp(2j * np.pi * np.array(beta) / 3))

    def mats(self, x, U0, W0):
        n = self.n
        m = n * n
        U = U0 @ expm(1j * herm(x[:m], n))
        W = W0 @ expm(1j * herm(x[m:2 * m], n))
        A = U @ self.Da @ U.conj().T
        B = W @ self.Db @ W.conj().T
        return A, B

    def resid(self, x, U0, W0, w, p):
        A, B = self.mats(x, U0, W0)
        r1, r2, C5 = words(A, B)
        E = C5 - np.eye(self.n)
        res = [w * E.real.ravel(), w * E.imag.ravel()]
        if p > 0:
            for r in (r1, r2):
                th = np.abs(angles(r))
                res.append(th ** p)
        return np.concatenate(res)


def solve(prob, rng, schedule=((1e2, 1), (1e3, 2), (1e4, 4), (1e5, 8), (1e6, 8))):
    n = prob.n
    U0, W0 = rand_unitary(n, rng), rand_unitary(n, rng)
    x = np.zeros(2 * n * n)
    # stage 0: land on the variety
    sol = least_squares(prob.resid, x, args=(U0, W0, 1.0, 0), method='lm', xtol=1e-15, ftol=1e-15, gtol=1e-15)
    A, B = prob.mats(sol.x, U0, W0)
    if np.linalg.norm(words(A, B)[2] - np.eye(n)) > 1e-8:
        return None
    for (w, p) in schedule:
        U0 = U0 @ expm(1j * herm(sol.x[:n * n], n))
        W0 = W0 @ expm(1j * herm(sol.x[n * n:], n))
        sol = least_squares(prob.resid, np.zeros(2 * n * n), args=(U0, W0, w, p), method='trf', xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=4000)
    # final exact projection back to the variety
    U0 = U0 @ expm(1j * herm(sol.x[:n * n], n))
    W0 = W0 @ expm(1j * herm(sol.x[n * n:], n))
    sol = least_squares(prob.resid, np.zeros(2 * n * n), args=(U0, W0, 1.0, 0), method='lm', xtol=1e-15, ftol=1e-15, gtol=1e-15)
    A, B = prob.mats(sol.x, U0, W0)
    r1, r2, C5 = words(A, B)
    res = np.linalg.norm(C5 - np.eye(n), 2)
    if res > 1e-10:
        return None
    return dict(d1=opdef(r1), d2=opdef(r2), res=res, A=A, B=B)


def irreducible(A, B, tol=1e-6):
    """Commutant dimension of the pair (A, B)."""
    n = A.shape[0]
    I = np.eye(n)
    M = np.vstack([np.kron(I, A) - np.kron(A.T, I), np.kron(I, B) - np.kron(B.T, I)])
    s = np.linalg.svd(M, compute_uv=False)
    return int(np.sum(s < tol * max(1, s[0])))


if __name__ == '__main__':
    n = int(sys.argv[1])
    alpha = [int(c) for c in sys.argv[2]]
    beta = [int(c) for c in sys.argv[3]]
    runs = int(sys.argv[4])
    seed = int(sys.argv[5])
    rng = np.random.default_rng(seed)
    prob = Problem(n, alpha, beta)
    best = None
    vals = []
    for t in range(runs):
        try:
            r = solve(prob, rng)
        except Exception as e:  # noqa
            r = None
        if r is None:
            continue
        v = max(r['d1'], r['d2'])
        vals.append(v)
        if best is None or v < best[0]:
            best = (v, r)
    if best is None:
        print(n, sys.argv[2], sys.argv[3], 'no-rep-found')
    else:
        v, r = best
        cd = irreducible(r['A'], r['B'])
        C = r['B'] @ r['A']
        ce = np.sort(np.round(np.angle(np.linalg.eigvals(C)) / (2 * np.pi) * 5).astype(int) % 5)
        print(n, sys.argv[2], sys.argv[3], 'found=%d best=%.6f d1=%.6f d2=%.6f res=%.1e commutant=%d Ctype=%s median=%.4f'
              % (len(vals), v, r['d1'], r['d2'], r['res'], cd, ''.join(map(str, ce)), float(np.median(vals))))
        np.savez('best_n%d_a%s_b%s.npz' % (n, sys.argv[2], sys.argv[3]), A=r['A'], B=r['B'])
