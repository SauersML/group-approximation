"""Sanity checks for torus-knot-k34-expander-pair-has-no-eigencorner.

For primes p, G_p = SL_2(F_p), S = [[0,-1],[1,0]], B = (ST)^2 with
T = [[1,1],[0,1]].  alpha, beta are the left-regular permutation unitaries
of S and B on l^2(G_p); D = diag(exp(i phi / 12)) with
phi(x) = pi * max(0, 1 - |x| / R), |x| the word length for the symmetric
set {S^{+-1}, B^{+-1}} acting on the left, R = floor(log_4 |G| / 2).
X = D^3 alpha, Y = D^4 beta.

The script checks, exactly or numerically:
  * in SL_2(Z): S^4 = I, B^3 = I, (ST)^3 = -I = S^2 and ST = B^{-1} S^2,
    so SL_2(Z) = <S, T> = <S, B>;
  * S has order 4 and B order 3 in G_p, and {S, B} generates G_p;
  * X^4 and Y^3 are diagonal, and ||X^4 - Y^3|| <= the commutator budget;
  * ||[D, alpha]||, ||[D, beta]|| <= pi / (12 R);
  * ||u - 1|| = 2 at the identity, tau(|u - 1|^2) and the support proportion;
  * the Kazhdan constant kappa = sqrt(2 (1 - mu)), mu the second eigenvalue
    of (1/4) sum_{s in Sigma} lambda(s), which stays bounded below.
It prints a table; it proves nothing asymptotic (R is tiny at these sizes).
"""
import math
from collections import deque

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as sla


def mat_mul(a, b, m=None):
    r = [[a[0][0] * b[0][0] + a[0][1] * b[1][0], a[0][0] * b[0][1] + a[0][1] * b[1][1]],
         [a[1][0] * b[0][0] + a[1][1] * b[1][0], a[1][0] * b[0][1] + a[1][1] * b[1][1]]]
    if m is not None:
        r = [[x % m for x in row] for row in r]
    return r


def key(a):
    return (a[0][0], a[0][1], a[1][0], a[1][1])


S = [[0, -1], [1, 0]]
T = [[1, 1], [0, 1]]
I2 = [[1, 0], [0, 1]]


def integer_checks():
    ST = mat_mul(S, T)
    B = mat_mul(ST, ST)
    S2 = mat_mul(S, S)
    S4 = mat_mul(S2, S2)
    B3 = mat_mul(mat_mul(B, B), B)
    ST3 = mat_mul(mat_mul(ST, ST), ST)
    Binv = mat_mul(B, B)  # B^3 = I so B^{-1} = B^2
    assert S4 == I2, S4
    assert B3 == I2, B3
    assert ST3 == [[-1, 0], [0, -1]] == S2
    assert mat_mul(Binv, S2) == ST
    # T = S^{-1} (ST) = S^3 (ST)
    assert mat_mul(mat_mul(S2, S), ST) == T
    return B


def run(p, B):
    elems = []
    idx = {}
    for a in range(p):
        for b in range(p):
            for c in range(p):
                for d in range(p):
                    if (a * d - b * c) % p == 1:
                        idx[(a, b, c, d)] = len(elems)
                        elems.append([[a, b], [c, d]])
    n = len(elems)
    assert n == p * (p * p - 1)
    Sp = [[x % p for x in row] for row in S]
    Bp = [[x % p for x in row] for row in B]
    Sinv = mat_mul(mat_mul(Sp, Sp, p), Sp, p)
    Binv = mat_mul(Bp, Bp, p)
    gens = [Sp, Sinv, Bp, Binv]
    # orders in G_p
    e = key([[1, 0], [0, 1]])
    assert key(mat_mul(mat_mul(Sp, Sp, p), mat_mul(Sp, Sp, p), p)) == e
    assert key(mat_mul(Sp, Sp, p)) != e
    assert key(mat_mul(mat_mul(Bp, Bp, p), Bp, p)) == e and key(Bp) != e
    # left multiplication tables
    left = []
    for g in gens:
        left.append(np.array([idx[key(mat_mul(g, x, p))] for x in elems]))
    # word length by BFS from identity
    dist = -np.ones(n, dtype=int)
    i0 = idx[e]
    dist[i0] = 0
    dq = deque([i0])
    while dq:
        v = dq.popleft()
        for tab in left:
            w = tab[v]
            if dist[w] < 0:
                dist[w] = dist[v] + 1
                dq.append(w)
    assert (dist >= 0).all(), "Sigma does not generate G_p"
    R = max(1, int(math.floor(math.log(n, 4) / 2)))
    phi = math.pi * np.maximum(0.0, 1.0 - dist / R)
    # permutation unitaries: (lambda(s) f)(x) = f(s^{-1} x), i.e. e_x -> e_{s x}
    def perm(tab):
        return sp.csr_matrix((np.ones(n), (tab, np.arange(n))), shape=(n, n))
    alpha = perm(left[0])
    beta = perm(left[2])
    Dd = np.exp(1j * phi / 12)
    D = sp.diags(Dd)
    X = D @ D @ D @ alpha
    Y = D @ D @ D @ D @ beta
    X4 = X @ X @ X @ X
    Y3 = Y @ Y @ Y
    u = D ** 12 if False else sp.diags(Dd ** 12)
    def opnorm_monomial(M):
        # all matrices here are monomial or differences of diagonals
        M = M.tocsr()
        M.eliminate_zeros()
        return float(np.abs(M.data).max()) if M.nnz else 0.0
    # X^4, Y^3 diagonal?
    for M in (X4, Y3):
        Mc = M.tocoo()
        assert np.all(Mc.row == Mc.col), "not diagonal"
    x4y3 = opnorm_monomial(X4 - Y3)
    x4u = opnorm_monomial(X4 - u)
    y3u = opnorm_monomial(Y3 - u)
    # commutators [D, alpha] = D alpha - alpha D is monomial
    cDa = opnorm_monomial(D @ alpha - alpha @ D)
    cDb = opnorm_monomial(D @ beta - beta @ D)
    w = np.abs(Dd ** 12 - 1) ** 2
    tau_w = float(w.mean())
    supp = float((phi > 0).mean())
    unorm = float(np.abs(Dd ** 12 - 1).max())
    # Kazhdan constant for regular rep via averaging operator
    M = sum(perm(t) for t in left) / 4.0
    M = (M + M.T) / 2
    vals = sla.eigsh(M, k=2, which="LA", return_eigenvectors=False)
    vals = np.sort(vals)
    mu = float(vals[0])
    kappa = math.sqrt(2 * (1 - mu))
    return dict(p=p, n=n, R=R, supp=supp, tau_w=tau_w, unorm=unorm,
                cDa=cDa, cDb=cDb, budget=math.pi / (12 * R) * 1.0000001,
                x4y3=x4y3, x4u=x4u, y3u=y3u, mu=mu, kappa=kappa)


def main():
    B = integer_checks()
    print("integer checks passed: S^4 = B^3 = I, (ST)^3 = -I, ST = B^-1 S^2, T = S^3 ST")
    hdr = "p     |G|    R  supp     tau|u-1|^2  ||u-1||  [D,a]    [D,b]    pi/12R   ||X4-Y3||  ||X4-u||  ||Y3-u||  mu      kappa"
    print(hdr)
    for p in [5, 7, 11, 13, 17, 19, 23, 29, 31]:
        r = run(p, B)
        assert r["cDa"] <= r["budget"] and r["cDb"] <= r["budget"]
        assert abs(r["unorm"] - 2) < 1e-12
        # proved budgets: ||X^4 - u|| <= 18 ||[D,a]||, ||Y^3 - u|| <= 12 ||[D,b]||
        assert r["x4u"] <= 18 * r["cDa"] + 1e-12 and r["y3u"] <= 12 * r["cDb"] + 1e-12
        print(f"{r['p']:<5} {r['n']:<6} {r['R']:<2} {r['supp']:.5f}  {r['tau_w']:.6f}    "
              f"{r['unorm']:.3f}    {r['cDa']:.5f}  {r['cDb']:.5f}  {r['budget']:.5f}  "
              f"{r['x4y3']:.5f}    {r['x4u']:.5f}   {r['y3u']:.5f}   {r['mu']:.4f}  {r['kappa']:.4f}")


if __name__ == "__main__":
    main()
