"""Regular roots of nonsingular equations over finite groups.

A word wbar = g0 t^e1 g1 ... t^eL gL over a finite group F (inside S_n),
a root tbar in S_n with wbar(tbar) = 1, the group F'' = <F, tbar>, and the
Fox derivative alpha = sum_k e_k s_k^(-1) in Z[F''] (s_k = prefix for t,
prefix*tbar^(-1) for t^(-1)).  The root is *regular* if alpha is a unit of
Q[F''] (equivalently a non-zero-divisor).  Unit test: full rank mod two
large primes of the |F''| x |F''| matrix M(x,y) = c(y x^(-1)).
"""
import itertools, random, sys, math
import numpy as np

def mul(a, b):
    return tuple(a[i] for i in b)
def inv(a):
    r = [0]*len(a)
    for i, x in enumerate(a):
        r[x] = i
    return tuple(r)
def ident(n):
    return tuple(range(n))
def closure(gens, n, cap=100000):
    e = ident(n)
    elems = [e]; idx = {e: 0}; k = 0
    while k < len(elems):
        g = elems[k]; k += 1
        for s in gens:
            h = mul(g, s)
            if h not in idx:
                idx[h] = len(elems); elems.append(h)
                if len(elems) > cap:
                    return None, None
    return elems, idx

def evalword(word, tb, n):
    u = ident(n); ti = inv(tb)
    for kind, v in word:
        if kind == 'g':
            u = mul(u, v)
        else:
            u = mul(u, tb if v == 1 else ti)
    return u

def alpha(word, tb, n):
    c = {}
    u = ident(n); ti = inv(tb)
    for kind, v in word:
        if kind == 'g':
            u = mul(u, v)
        elif v == 1:
            s = u; c[inv(s)] = c.get(inv(s), 0) + 1; u = mul(u, tb)
        else:
            u = mul(u, ti); s = u; c[inv(s)] = c.get(inv(s), 0) - 1
    return {k: v for k, v in c.items() if v != 0}

def rank_modp(M, p):
    A = M.copy() % p
    nr, nc = A.shape; r = 0
    for col in range(nc):
        piv = np.nonzero(A[r:, col])[0]
        if len(piv) == 0:
            continue
        pr = r + piv[0]
        if pr != r:
            A[[r, pr]] = A[[pr, r]]
        invp = pow(int(A[r, col]), p - 2, p)
        A[r] = (A[r] * invp) % p
        rows = np.nonzero(A[:, col])[0]
        rows = rows[rows != r]
        if len(rows):
            A[rows] = (A[rows] - np.outer(A[rows, col], A[r])) % p
        r += 1
        if r == nr:
            break
    return r

def is_unit(c, elems, idx):
    N = len(elems)
    M = np.zeros((N, N), dtype=np.int64)
    for x in range(N):
        gx = elems[x]
        for rho, v in c.items():
            M[x, idx[mul(rho, gx)]] += v
    for p in (32749, 32719):
        if rank_modp(M, p) == N:
            return True
    return False

def regular_root(word, F_gens, n, cap):
    Sn = list(itertools.permutations(range(n)))
    found_root = False
    for tb in Sn:
        if evalword(word, tb, n) != ident(n):
            continue
        found_root = True
        elems, idx = closure(list(F_gens) + [tb], n, cap)
        if elems is None:
            continue
        c = alpha(word, tb, n)
        if is_unit(c, elems, idx):
            return True, tb, len(elems)
    return found_root, None, None

def random_word(F, L, rng):
    while True:
        es = [rng.choice([1, -1]) for _ in range(L)]
        if sum(es) != 0:
            break
    w = [('g', rng.choice(F))]
    for e in es:
        w.append(('t', e)); w.append(('g', rng.choice(F)))
    return w

def fmt(word):
    out = []
    for kind, v in word:
        if kind == 't':
            out.append('t' if v == 1 else 'T')
        else:
            out.append(str(v))
    return ' '.join(out)

def is_unit_fast(c, elems, idx):
    """Sparse float LU screen; confirm borderline cases mod p."""
    import scipy.sparse as sp
    import scipy.sparse.linalg as spl
    N = len(elems)
    rows, cols, vals = [], [], []
    for x in range(N):
        gx = elems[x]
        for rho, v in c.items():
            rows.append(x); cols.append(idx[mul(rho, gx)]); vals.append(float(v))
    M = sp.csc_matrix((vals, (rows, cols)), shape=(N, N))
    try:
        lu = spl.splu(M)
    except RuntimeError:
        return False
    d = np.abs(lu.U.diagonal())
    if d.min() > 1e-6:
        return True
    if N <= 1500:
        return is_unit(c, elems, idx)
    return None

def regular_root_iter(word, F_gens, n, cap, roots_iter=None):
    """Like regular_root but over an arbitrary iterator of candidate roots."""
    found_root = False; undecided = 0
    for tb in (roots_iter if roots_iter is not None else itertools.permutations(range(n))):
        if evalword(word, tb, n) != ident(n):
            continue
        found_root = True
        elems, idx = closure(list(F_gens) + [tb], n, cap)
        if elems is None:
            continue
        u = is_unit_fast(alpha(word, tb, n), elems, idx)
        if u:
            return True, tb, len(elems)
        if u is None:
            undecided += 1
    return found_root, None, undecided
