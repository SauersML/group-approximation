"""Abelianized colimit of cabling stabilizers over a strict fundamental domain.

Rings: 0..n-1.
- A vertex of the fundamental domain is an ordered pair (a, b) of rings.
- Its stabilizer is P_(a,b) ~ PSigmaAut on the ring set R - {a, b} + {f}.
- H_1(PSigmaAut_R) is free abelian on the A_pq (p != q in R).
- Cabling the ring f onto the pair (a, b), in abelianized form (Lemma 5.1 of the colimit proof):
    A_pq -> A_pq
    A_pf -> A_pa + A_pb
    A_fq -> A_aq + A_bq
- Edge {u, u'} (disjoint pairs): the edge group lives on ring set R - u - u' + {f1, f2}.

The abelianized colimit is  (+)_v H_1(P_v)  modulo  { i_u(x) - i_u'(x) : x in H_1(P_e) }.
Colimits commute with abelianization, and higher faces factor through edges.

We compare its rank with rank H_1(P) = n(n-1). If the colimit rank is larger, then
colim != P, so pi_1 of the development (an X_n(F)- or Y-type complex) is nonzero, whenever the
fundamental domain is simply connected.

Ranks are computed mod several primes; a prime-dependent answer signals torsion.
"""
import itertools
import sys

import numpy as np


def rank_mod_p(M, p):
    M = M.copy() % p
    r = 0
    rows, cols = M.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c]:
                piv = i
                break
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        nz = np.nonzero(M[:, c])[0]
        for i in nz:
            if i != r:
                M[i] = (M[i] - M[i, c] * M[r]) % p
        r += 1
        if r == rows:
            break
    return r


def gens(R):
    return [(p, q) for p in R for q in R if p != q]


def cable(vec, f, a, b):
    """Push a dict {(p, q): coef} through cabling ring f onto the pair (a, b)."""
    out = {}
    for (p, q), c in vec.items():
        if p == f:
            imgs = [(a, q), (b, q)]
        elif q == f:
            imgs = [(p, a), (p, b)]
        else:
            imgs = [(p, q)]
        for g in imgs:
            out[g] = out.get(g, 0) + c
    return out


def colimit_rank(n, verts, primes=(2, 3, 5, 7, 1000003)):
    R = list(range(n))
    vidx = {}      # (vertex, generator) -> column
    vrings = {}
    for v in verts:
        Rv = [r for r in R if r not in v] + [('f', v)]
        vrings[v] = Rv
        for g in gens(Rv):
            vidx[(v, g)] = len(vidx)
    rows = []
    for u, u2 in itertools.combinations(verts, 2):
        if set(u) & set(u2):
            continue
        f1, f2 = ('f', u), ('f', u2)
        Re = [r for r in R if r not in u and r not in u2] + [f1, f2]
        for g in gens(Re):
            # into u's group: cable f2 onto u2 (f1 stays as u's fused ring)
            x1 = cable({g: 1}, f2, *u2)
            x2 = cable({g: 1}, f1, *u)
            row = np.zeros(len(vidx), dtype=np.int64)
            for h, c in x1.items():
                row[vidx[(u, h)]] += c
            for h, c in x2.items():
                row[vidx[(u2, h)]] -= c
            rows.append(row)
    M = np.array(rows, dtype=np.int64) if rows else np.zeros((0, len(vidx)), dtype=np.int64)
    return {p: len(vidx) - rank_mod_p(M, p) for p in primes}, n * (n - 1)


def domain(n, F, mode, v=None, w=None):
    free = [r for r in range(n) if r not in F]
    if mode == 'QF':
        return [(a, b) for a in free for b in free if a != b]
    if mode == 'X0':
        fr = [r for r in free if r not in (v, w)]
        return [(a, b) for a in fr for b in fr if a != b]
    if mode == 'Y':
        fr = [r for r in free if r not in (v, w)]
        return [(a, b) for a in fr for b in fr if a != b] + [(v, w), (w, v)]
    raise ValueError(mode)


if __name__ == '__main__':
    cases = [(int(a), int(b), m) for a, b, m in (s.split(':') for s in sys.argv[1:])]
    for n, nf, mode in cases:
        F = list(range(n - nf, n))
        free = [r for r in range(n) if r not in F]
        verts = domain(n, F, mode, v=free[0], w=free[1])
        res, target = colimit_rank(n, verts)
        print(f"n={n} |F|={nf} N={n-nf} mode={mode}: colim^ab rank mod p = {res}; "
              f"H1(P) rank = {target}", flush=True)
