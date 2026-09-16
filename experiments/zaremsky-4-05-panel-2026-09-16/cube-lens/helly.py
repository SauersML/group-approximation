"""Adversarial search for Helly-number failures of vertex-centred d_1-balls in |X|.

For centres z_0..z_n and Helly order q (q = k+1 for the claim, q = k as power check):
failure  <=>  exists rho with every q-subfamily meeting and the whole family empty.
In the box E (by Corollary Rt this is the same question) the whole family is empty iff
some lambda in the simplex has  lambda.rho < g(lambda) := min_{c in E} sum_i lambda_i L_{z_i}(c).
For fixed lambda,  min lambda.rho  subject to  (for all q-subsets T: exists c_T in E with
L_{z_i}(c_T) <= rho_i, i in T)  is an LP.  F(lambda) = g(lambda) - LPmin(lambda) > 0 is a
failure certificate.  We maximise F over lambda by random restarts + local search, and
re-verify any candidate failure directly in |X| (union of maximal cubes), independently of
Corollary Rt.
Usage: python3 helly.py seed iters_per_graph [q_offset]   (q = k+1+q_offset)
"""
import sys, random, itertools
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
from graphs import zoo


def g_of(G, Z, lam):
    tot = 0.0
    lin = np.zeros(G.m)
    for z, l in zip(Z, lam):
        a, const = G.Lcoef(z)
        tot += l * const
        lin += l * a
    return tot + np.minimum(lin, 0).sum()


def inner(G, Z, lam, q):
    n1 = len(Z)
    subsets = list(itertools.combinations(range(n1), q))
    nT = len(subsets)
    nvar = n1 + nT * G.m
    rows = sum(len(T) for T in subsets)
    A = lil_matrix((rows, nvar))
    b = np.zeros(rows)
    r = 0
    coefs = [G.Lcoef(z) for z in Z]
    for t, T in enumerate(subsets):
        off = n1 + t * G.m
        for i in T:
            a, const = coefs[i]
            for h in range(G.m):
                A[r, off + h] = a[h]
            A[r, i] = -1.0
            b[r] = -const
            r += 1
    cvec = np.concatenate([np.array(lam, dtype=float), np.zeros(nT * G.m)])
    bounds = [(None, None)] * n1 + [(0, 1)] * (nT * G.m)
    res = linprog(cvec, A_ub=A.tocsr(), b_ub=b, bounds=bounds, method="highs")
    return res.fun, res.x[:n1]


def F(G, Z, lam, q):
    val, rho = inner(G, Z, lam, q)
    return g_of(G, Z, lam) - val, rho


def verify_X(G, Z, rho, q):
    """Direct check in |X|: every q-subfamily meets, whole family does not."""
    full, _ = G.lp_minmax_X(Z, rho)
    subs = max(G.lp_minmax_X([Z[i] for i in T], [rho[i] for i in T])[0]
               for T in itertools.combinations(range(len(Z)), q))
    return full, subs


def search(G, rng, iters, q, ncent):
    best = (-np.inf, None, None, None)
    for it in range(iters):
        Z = rng.sample(range(G.n), ncent)
        lam = np.array([rng.random() for _ in Z])
        lam /= lam.sum()
        val, rho = F(G, Z, lam, q)
        step = 0.3
        for _ in range(25):
            lam2 = np.maximum(lam + rng.gauss(0, 1) * step * (np.array([rng.random() for _ in Z]) - 0.5), 1e-6)
            lam2 /= lam2.sum()
            v2, r2 = F(G, Z, lam2, q)
            if v2 > val + 1e-12:
                lam, val, rho = lam2, v2, r2
            else:
                step *= 0.85
        if val > best[0]:
            best = (val, Z, lam, rho)
    return best


if __name__ == "__main__":
    seed = int(sys.argv[1])
    iters = int(sys.argv[2])
    qoff = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    extra = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    names = sys.argv[5].split(",") if len(sys.argv) > 5 else None
    rng = random.Random(seed)
    for G in zoo(seed):
        if names and G.name not in names:
            continue
        q = G.k + 1 + qoff
        if q < 1:
            continue
        ncent = q + 1 + extra
        if ncent > G.n:
            continue
        val, Z, lam, rho = search(G, rng, iters, q, ncent)
        line = "%s n=%d m=%d k=%d q=%d centres=%d bestF=%.3g" % (G.name, G.n, G.m, G.k, q, ncent, val)
        if val > 1e-7:
            full, subs = verify_X(G, Z, list(rho), q)
            line += " | X-check: full=%.4g max_q_sub=%.4g Z=%s rho=%s" % (full, subs, Z, np.round(rho, 4).tolist())
        print(line, flush=True)
