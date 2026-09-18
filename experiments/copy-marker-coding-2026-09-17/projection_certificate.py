"""Search for an infinite-window certificate that the conjugation projection of the B_1 coded pair
in F_2 is unbalanced.

We look for phi: F_2 -> [-1/2, 1/2] of finite type and delta > 0 with
    (1/K) sum_{g in B_1} [ phi(g D g^-1) - phi(g D) ] >= delta   for EVERY D in F_2.
Then for every finitely supported mu, TV(C mu, L mu) >= delta, hence for every nu on F_2 x F_2
TV(alpha nu, beta nu) >= delta (push-forward under (x, w) -> w x^{-1}).

Type of w: w itself if |w| <= L, else (first p letters, last p letters), with L = 2p+3.
Every D with |D| <= L+2 is an explicit constraint. A D with |D| >= L+3 has all images of length
> L, and their types depend only on the first p+1 and last p+1 letters of D, so one representative
of length L+3 per (prefix, suffix) pair covers all of them. Symmetry: phi is taken invariant under
the 8 signed generator permutations (averaging a solution keeps it a solution).
Run: python3 projection_certificate.py p
"""
import sys
import time
import itertools
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog
from coded_pair_lp import ball, mul, INV, GENS
from coded_pair_lp_sym import MAPS
from conjugation_projection_lp import inv

S = ['', 'a', 'A', 'b', 'B']
K = len(S)


def reduced_words(n):
    return [w for w in ball(n) if len(w) == n]


def make_type(p, L):
    def typ(w):
        if len(w) <= L:
            return ('S', min(w.translate(t) for t in MAPS))
        return ('L',) + min((w[:p].translate(t), w[-p:].translate(t)) for t in MAPS)
    return typ


def connect(P, Q, m):
    """Reduced word P + x + Q with |x| = m (m >= 2)."""
    for x in itertools.product(GENS, repeat=m):
        w = P + ''.join(x) + Q
        if all(w[i] != INV[w[i + 1]] for i in range(len(w) - 1)):
            return w
    raise ValueError


def solve(p):
    L = 2 * p + 3
    typ = make_type(p, L)
    t0 = time.time()
    cons = []
    seen = set()
    for D in ball(L + 2):
        c = min(D.translate(t) for t in MAPS)
        if c not in seen:
            seen.add(c); cons.append(c)
    pre = reduced_words(p + 1)
    seenL = set()
    for P in pre:
        for Q in pre:
            key = min((P.translate(t), Q.translate(t)) for t in MAPS)
            if key in seenL:
                continue
            seenL.add(key)
            cons.append(connect(key[0], key[1], L + 3 - 2 * (p + 1)))
    var = {}
    rows, cols, vals = [], [], []
    for r, D in enumerate(cons):
        for g in S:
            for w, s in ((mul(mul(g, D), inv(g)), 1.0), (mul(g, D), -1.0)):
                tp = typ(w)
                if tp not in var:
                    var[tp] = len(var)
                rows.append(r); cols.append(var[tp]); vals.append(-s / K)
    nv, R = len(var), len(cons)
    M = sp.csr_matrix((vals, (rows, cols)), shape=(R, nv))
    M.sum_duplicates()
    # variables: phi (nv), delta; constraint: delta + M phi <= 0 ; maximize delta
    Aub = sp.hstack([M, sp.csr_matrix(np.ones((R, 1)))], format='csr')
    c = np.zeros(nv + 1); c[-1] = -1.0
    bounds = [(-0.5, 0.5)] * nv + [(None, 1.0)]
    res = linprog(c, A_ub=Aub, b_ub=np.zeros(R), bounds=bounds, method='highs')
    return -res.fun, nv, R, time.time() - t0, res, var, cons


if __name__ == '__main__':
    for p in [int(a) for a in sys.argv[1:]]:
        delta, nv, R, tm, res, var, cons = solve(p)
        print(f'p={p} L={2*p+3} types={nv} constraints={R} delta={delta:.6f} time={tm:.0f}s', flush=True)
