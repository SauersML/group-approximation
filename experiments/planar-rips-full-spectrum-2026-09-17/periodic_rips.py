#!/usr/bin/env python3
"""Twisted homology of Rips complexes of translation-periodic planar patterns.

A periodic pattern is a finite motif M = {m_0..m_{k-1}} in R^2 and a period
vector v; Y = {m_i + j v : i < k, j in Z}.  The Rips complex R_r(Y) (closed
convention, clique complex of the r-graph) carries a free Z-action by v.  Its
quotient K is a finite Delta-complex.  For lambda in a field F the twisted
chain complex C_*(K; F_lambda) has one basis vector per orbit of cliques and
boundary coefficients sign * lambda^s, where s is the period shift of a face.

Certificate (see research/planar-rips-periodic-strip-bending.md):
if b_2(K; F_lambda) differs for two values of lambda, then H_2(R_r(Y); Q)
is not a free Q[t^{+-1}]-module (after an exact check over Q), and every
sufficiently fine bending of the pattern around a large circle is a finite
planar set whose Rips complex is not a wedge of spheres.

Abstract periodic graphs are also accepted (for testing): vertices are
orbit labels 0..k-1, edges are triples (i, i2, s) meaning (i, j) ~ (i2, j+s).
"""
import itertools
import math
import random
import sys

P = 2147483629  # prime below 2^31


def periodic_graph_from_points(motif, v, r, eps=0.0):
    """Edges (i, i2, s) with |m_i - m_i2 - s v| <= r, stored for s >= 0
    (and i < i2 when s == 0).  Returns (k, adj) where adj[i] is a set of
    (i2, s) meaning (i,0) ~ (i2,s), for all s in Z."""
    k = len(motif)
    vx, vy = v
    vn = math.hypot(vx, vy)
    diam = max(math.dist(a, b) for a in motif for b in motif) if k > 1 else 0
    S = int(math.ceil((r + diam) / vn)) + 1
    adj = [set() for _ in range(k)]
    margin = float('inf')
    for i in range(k):
        for i2 in range(k):
            for s in range(-S, S + 1):
                if s == 0 and i == i2:
                    continue
                dx = motif[i2][0] + s * vx - motif[i][0]
                dy = motif[i2][1] + s * vy - motif[i][1]
                d = math.hypot(dx, dy)
                margin = min(margin, abs(d - r))
                if d <= r:
                    adj[i].add((i2, s))
    return k, adj, margin


def cliques(k, adj, maxsize):
    """Orbit representatives of cliques of size <= maxsize: tuples of
    (i, s) sorted by (s, i), whose first vertex has s == 0."""
    def nb(vtx):
        i, s = vtx
        return {(i2, s + t) for (i2, t) in adj[i]}
    out = {1: [((i, 0),) for i in range(k)]}
    frontier = [(((i, 0),), {w for w in nb((i, 0)) if (w[1], w[0]) > (0, i)})
                for i in range(k)]
    for size in range(2, maxsize + 1):
        new = []
        lst = []
        for cl, cand in frontier:
            last = cl[-1]
            for w in cand:
                if (w[1], w[0]) <= (last[1], last[0]):
                    continue
                cl2 = cl + (w,)
                cand2 = cand & nb(w)
                new.append((cl2, cand2))
                lst.append(cl2)
        out[size] = lst
        frontier = new
    return out


def normalize(face):
    s0 = min(w[1] for w in face)
    f = tuple(sorted(((i, s - s0) for (i, s) in face), key=lambda w: (w[1], w[0])))
    return f, s0


def boundary_entries(cells_hi, index_lo):
    """Sparse boundary: list of rows (one per high cell) of (col, sign, shift)."""
    rows = []
    for cl in cells_hi:
        row = []
        for pos in range(len(cl)):
            face = cl[:pos] + cl[pos + 1:]
            f, s0 = normalize(face)
            row.append((index_lo[f], -1 if pos % 2 else 1, s0))
        rows.append(row)
    return rows


def rank_mod_p(rows, ncols, lam, p=P):
    """Rank of the matrix with entries sign*lam^shift, via sparse elimination."""
    pivots = {}  # col -> row dict
    rank = 0
    lampow = {}
    for row in rows:
        vec = {}
        for (c, sg, sh) in row:
            if sh not in lampow:
                lampow[sh] = pow(lam, sh, p)
            vec[c] = (vec.get(c, 0) + sg * lampow[sh]) % p
        vec = {c: x for c, x in vec.items() if x}
        while vec:
            c = min(vec)
            if c in pivots:
                prow = pivots[c]
                f = vec[c]
                for c2, x in prow.items():
                    y = (vec.get(c2, 0) - f * x) % p
                    if y:
                        vec[c2] = y
                    else:
                        vec.pop(c2, None)
            else:
                inv = pow(vec[c], p - 2, p)
                pivots[c] = {c2: (x * inv) % p for c2, x in vec.items()}
                rank += 1
                break
    return rank


def twisted_betti(k, adj, lams, top=3, p=P):
    cl = cliques(k, adj, top + 1)
    index = {d: {c: n for n, c in enumerate(cl[d + 1])} for d in range(top + 1)}
    bnd = {d: boundary_entries(cl[d + 1], index[d - 1]) for d in range(1, top + 1)}
    sizes = [len(cl[d + 1]) for d in range(top + 1)]
    res = {}
    for lam in lams:
        rk = {d: rank_mod_p(bnd[d], sizes[d - 1], lam, p) for d in range(1, top + 1)}
        rk[0] = 0
        rk[top + 1] = None
        b = []
        for d in range(top):
            b.append(sizes[d] - rk[d] - rk[d + 1])
        res[lam] = b
    return sizes, res


def reduce_periodic(k, adj):
    """Remove orbits of vertices dominated by a vertex of another orbit
    (N[(i,0)] subset of N[(i2,s)]), repeatedly.  Valid for every bending with
    many periods: the copies are removed one at a time, each still dominated."""
    alive = set(range(k))
    changed = True
    def closed_nb(i):
        return {(i2, s) for (i2, s) in adj[i] if i2 in alive} | {(i, 0)}
    while changed:
        changed = False
        for i in sorted(alive):
            Ni = closed_nb(i)
            for (i2, s) in adj[i]:
                if i2 == i or i2 not in alive:
                    continue
                Nj = {(a, b + s) for (a, b) in closed_nb(i2)}
                if Ni <= Nj:
                    alive.discard(i)
                    changed = True
                    break
    old = sorted(alive)
    ren = {o: n for n, o in enumerate(old)}
    nadj = [set((ren[i2], s) for (i2, s) in adj[o] if i2 in alive) for o in old]
    return len(old), nadj, old


if __name__ == "__main__":
    print("module; see search scripts")
