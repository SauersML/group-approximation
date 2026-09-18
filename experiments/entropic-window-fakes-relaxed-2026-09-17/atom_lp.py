#!/usr/bin/env python3
"""Linear-atom LP: minimise Phi over nonnegative combinations of rank functions of one-bit F_2-linear configurations.

usage: atom_lp.py target.txt [maxdim]   (file from relaxed_target.py; maxdim bounds each codeword subspace dimension)

An atom: every x_g is one bit (d = 1); codeword y_j is a subspace of F_2^(reads of j) (any dimension, including 0).
Its entropy vector h_a(S) = |S_x| + rank(rows of the codewords in S, with the coordinates of S_x deleted).
A nonnegative rational combination sum_a w_a h_a with sum_a w_a = 1 is the entropy vector of a direct sum of
independent copies (multiplicities w_a * D for a common denominator D), in units of D bits per x_g, so it is
entropic. (I) and (D) hold atom by atom; (T) is imposed on the combination only:
    sum_a w_a (h_a(S) - h_a(rep(S))) = 0     for every subset S.
So an LP value < 1 exhibits an F_2-linear (hence entropic) fake, with no need for any atom to be invariant.
Prints the value and the support of an optimal combination.
"""
import sys, itertools
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix


def rref_subspaces(k):
    """All subspaces of F_2^k, each as a tuple of basis vectors (ints)."""
    out = set()
    vecs = list(range(1, 1 << k))
    def reduce(basis):
        b = []
        for v in basis:
            for w in b:
                v = min(v, v ^ w)
            if v:
                b.append(v); b.sort(reverse=True)
        # full reduction for canonical form
        b = sorted(b, reverse=True)
        for i in range(len(b)):
            for j in range(len(b)):
                if i != j and (b[j] ^ b[i]) < b[j] and (b[i].bit_length() <= b[j].bit_length()):
                    hb = 1 << (b[i].bit_length() - 1)
                    if b[j] & hb:
                        b[j] ^= b[i]
        return tuple(sorted(b, reverse=True))
    frontier = {()}
    out.add(())
    while frontier:
        nxt = set()
        for B in frontier:
            span = {0}
            for v in B:
                span |= {s ^ v for s in span}
            for v in vecs:
                if v not in span:
                    C = reduce(list(B) + [v])
                    if C not in out:
                        out.add(C); nxt.add(C)
        frontier = nxt
    return sorted(out, key=lambda B: (len(B), B))


def rank2(rows):
    basis = []
    for v in rows:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v); basis.sort(reverse=True)
    return len(basis)


def load(path):
    with open(path) as f:
        m, r = map(int, f.readline().split())
        reads = []
        for _ in range(r):
            t = list(map(int, f.readline().split())); reads.append(t[1:])
        col = list(map(int, f.readline().split()))
        my0, mx1yF, myF = map(int, f.readline().split())
    return m, r, reads, col, my0, mx1yF, myF


def atom_vector(m, r, codes, N):
    h = np.zeros(N)
    for S in range(N):
        keep = 0; nx = 0
        for g in range(m):
            if S >> g & 1:
                nx += 1
            else:
                keep |= 1 << g
        rows = []
        for j in range(r):
            if S >> (m + j) & 1:
                rows += [v & keep for v in codes[j]]
        h[S] = nx + rank2(rows)
    return h


def main():
    m, r, reads, col, my0, mx1yF, myF = load(sys.argv[1])
    N = 1 << (m + r)
    rep = {}
    for S in range(N):
        rep.setdefault(col[S], S)
    subs = {}
    per = []
    for j in range(r):
        k = len(reads[j])
        if k not in subs:
            maxdim = int(sys.argv[2]) if len(sys.argv) > 2 else k
            subs[k] = [B for B in rref_subspaces(k) if len(B) <= maxdim]
        # embed: bit i of the local subspace -> block reads[j][i]
        emb = []
        for B in subs[k]:
            emb.append(tuple(sum(1 << reads[j][i] for i in range(k) if v >> i & 1) for v in B))
        per.append(sorted(set(emb)))
    atoms = list(itertools.product(*per))
    print('atoms', len(atoms), 'subsets', N, flush=True)
    H = np.array([atom_vector(m, r, a, N) for a in atoms]).T  # N x A
    pairs = [S for S in range(N) if rep[col[S]] != S]
    A_eq = np.vstack([H[pairs] - H[[rep[col[S]] for S in pairs]], np.ones((1, len(atoms)))])
    b_eq = np.zeros(len(pairs) + 1); b_eq[-1] = 1.0
    c = H[my0] + H[mx1yF] - H[myF]
    res = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method='highs')
    print('status', res.status, 'value', res.fun)
    if res.status == 0:
        for i in np.nonzero(res.x > 1e-9)[0]:
            print('  w=%.6f phi=%g codes=%s' % (res.x[i], c[i], [list(map(bin, cd)) for cd in atoms[i]]))


if __name__ == '__main__':
    main()
