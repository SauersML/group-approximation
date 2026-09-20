"""Spectral relaxation of the full-hyperedge count on a random level.

For A in atoms with type densities alpha_i, and any convex weights c_{k,p}
on the three pairs p of each triangle type k,
    F(A) <= sum_{k,p} c_{k,p} #{q : both atoms of pair p of (q,k) in A}
          = <1_A, P 1_A>,   P = sym. sum c_{k,p} E_{i,i'} (x) U_{g}.
Writing 1_A = constants + f:  <1_A,P1_A> = n a^T B a + <f,Pf>,
    <f,Pf> <= lam * n * sum_i a_i (1 - a_i),  lam = top eig of P on l2_0 (x) C^R.
The closure argument (Lemma 1 of the (W) proof) needs, at some stage
mu = |C|/n in (0,1], sup_a [a^T B a + lam sum a_i(1-a_i)] < mu.
This script computes B, lam (uniform weights 1/3) and that sup at mu=1/2.
Usage: python3 spectral.py j n seed
"""
import sys
import random
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as sla
from hyper import build, instantiate, random_level


def operator(M, PA, PB, weights=None):
    n, R = len(PA), M['R']
    H = instantiate(M, PA, PB)
    K = len(M['hyp'])
    rows, cols, vals = [], [], []
    for h, (x, y, z) in enumerate(H):
        k = h // n
        w = weights[k] if weights is not None else (1 / 3, 1 / 3, 1 / 3)
        for (u, v), c in zip(((x, y), (y, z), (x, z)), w):
            rows += [u, v]
            cols += [v, u]
            vals += [c / 2, c / 2]
    P = sp.csr_matrix((vals, (rows, cols)), shape=(n * R, n * R))
    return P, H, K


def analyse(j, n, seed):
    rng = random.Random(seed)
    M = build(j)
    R = M['R']
    PA, PB = random_level(n, rng)
    P, H, K = operator(M, PA, PB)
    # constants block B: B[i,i'] = (1/n) 1_i^T P 1_i'
    E = sp.csr_matrix((np.ones(n * R), (np.arange(n * R), np.arange(n * R) % R)),
                      shape=(n * R, R))
    B = (E.T @ (P @ E)).toarray() / n
    Q = E.toarray() / np.sqrt(n)   # orthonormal basis of constants

    def mv(v):
        v = v - Q @ (Q.T @ v)
        w = P @ v
        return w - Q @ (Q.T @ w)
    L = sla.LinearOperator((n * R, n * R), matvec=mv, dtype=float)
    top = sla.eigsh(L, k=3, which='LA', return_eigenvectors=False)
    lam = max(top)
    degs = np.asarray(P.sum(axis=1)).ravel()
    return M, B, lam, degs


def sup_at(B, lam, mu, trials=2000, seed=0):
    """Max of a^T B a + lam sum a(1-a) over a in [0,1]^R, sum a = mu
    (projected gradient ascent with restarts; a lower bound on the sup)."""
    rng = np.random.default_rng(seed)
    R = B.shape[0]
    best = -1
    for _ in range(trials):
        a = rng.dirichlet(np.ones(R) * rng.choice([0.1, 1, 10])) * mu
        a = np.minimum(a, 1)
        for _ in range(200):
            g = 2 * B @ a + lam * (1 - 2 * a)
            a = a + 0.05 * g
            # project to box and simplex slice by bisection on shift
            lo, hi = -10, 10
            for _ in range(50):
                s = (lo + hi) / 2
                if np.clip(a - s, 0, 1).sum() > mu:
                    lo = s
                else:
                    hi = s
            a = np.clip(a - hi, 0, 1)
        val = a @ B @ a + lam * (a * (1 - a)).sum()
        best = max(best, val)
    return best


if __name__ == '__main__':
    j, n, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    M, B, lam, degs = analyse(j, n, seed)
    R = M['R']
    print('j', j, 'n', n, 'R', R, 'triangle types', len(M['hyp']))
    print('row sums of B (hyperedge pair-weight per atom type):',
          np.round(B.sum(axis=1), 3))
    print('lawful type', M['lawful'].index(True), 'B_LL', round(B[M['lawful'].index(True)].sum(), 3))
    print('top eigenvalue of B', round(max(np.linalg.eigvalsh(B)), 4))
    print('lam (top eig of P on l2_0 x C^R)', round(lam, 4))
    for mu in (0.1, 0.25, 0.5, 1.0):
        s = sup_at(B, lam, mu, trials=200)
        print('mu', mu, 'sup_a bound', round(s, 4), 'slack mu - sup', round(mu - s, 4))
