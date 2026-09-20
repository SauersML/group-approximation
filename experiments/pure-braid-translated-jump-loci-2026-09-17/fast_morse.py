#!/usr/bin/env python3
"""Fast version of salvetti_morse.py (same mathematics, integer arithmetic).

Cells of the Salvetti complex X of the braid arrangement: <C', F> with F <= C'.
With the cocycle d(edge across H_ij) = a_ij + eta(head) - eta(tail) (the factor 1/2 of
salvetti_morse.py is absorbed by doubling a; this represents 2 chi, the same ray), the
lifted vertex heights of <C', F> relative to C' are
    f(D) = sum_{ij separating C', D} a_ij + eta(D),   D in star(F).
Each cell of positive dimension has a lowest vertex (required unique); it lies in the
ascending link of exactly that vertex.  Asc(C) = cells with lowest vertex C.
Bestvina--Brady: Asc(C) (m-1)-acyclic for all C  =>  [chi] in Sigma^m(P_n; Z)
(over the coefficient field used; see note on primes below), and (m-1)-connected
=> [chi] in Sigma^m(P_n)."""
import itertools, random
import numpy as np

def pairs(n):
    return [(a, b) for a in range(n) for b in range(a + 1, n)]

class Salvetti:
    def __init__(self, n):
        self.n = n
        self.ch = list(itertools.permutations(range(n)))
        self.ci = {c: i for i, c in enumerate(self.ch)}
        N = len(self.ch)
        P = pairs(n)
        pos = np.array([[c.index(x) for x in range(n)] for c in self.ch])  # pos[c][x]
        # side[c, p] = 1 if i before j in chamber c
        side = np.array([[pos[c][i] < pos[c][j] for (i, j) in P] for c in range(N)], dtype=np.int8)
        self.side = side
        self.P = P
        # cells
        self.cells = []  # (Cp index, F) with F tuple of frozensets
        self.cell_index = {}
        self.stars = {}
        for ci, C in enumerate(self.ch):
            for cuts in itertools.product((0, 1), repeat=n - 1):
                blocks, cur = [], [C[0]]
                for i in range(1, n):
                    if cuts[i - 1]:
                        blocks.append(frozenset(cur)); cur = [C[i]]
                    else:
                        cur.append(C[i])
                blocks.append(frozenset(cur))
                F = tuple(blocks)
                if F not in self.stars:
                    st = [()]
                    for B in F:
                        st = [r + p for r in st for p in itertools.permutations(sorted(B))]
                    self.stars[F] = np.array([self.ci[s] for s in st])
                self.cell_index[(ci, F)] = len(self.cells)
                self.cells.append((ci, F))
        self.dim = [n - len(F) for (_, F) in self.cells]
        # faces (codim-1 and all) of each cell: <D,G> <= <C',F> iff G refines F and D = G o C'
        self.faces = [[] for _ in self.cells]
        for k, (ci, F) in enumerate(self.cells):
            C = self.ch[ci]
            p = {x: i for i, x in enumerate(C)}
            for G in self.refinements(F):
                D = tuple(x for B in G for x in sorted(B, key=p.get))
                j = self.cell_index[(self.ci[D], G)]
                if j != k:
                    self.faces[k].append(j)

    def refinements(self, F):
        """all ordered set partitions refining F (block order kept)"""
        opts = [self.ordered_partitions(sorted(B)) for B in F]
        for combo in itertools.product(*opts):
            yield tuple(b for part in combo for b in part)

    def ordered_partitions(self, S):
        S = list(S)
        if not S:
            return [()]
        out = []
        for r in range(1, len(S) + 1):
            for first in itertools.combinations(S, r):
                rest = [x for x in S if x not in first]
                for tail in self.ordered_partitions(rest):
                    out.append((frozenset(first),) + tail)
        return out

    def lowest(self, a, eta):
        """a: vector over pairs (ints); eta: vector over chambers (ints).
        Returns array low[cell] (chamber index), raising on ties."""
        av = np.array([a[p] for p in self.P], dtype=np.int64)
        low = np.empty(len(self.cells), dtype=np.int64)
        for k, (ci, F) in enumerate(self.cells):
            st = self.stars[F]
            sep = (self.side[st] != self.side[ci])  # |st| x pairs
            f = sep.astype(np.int64) @ av + eta[st]
            j = np.argmin(f)
            if (f == f[j]).sum() > 1:
                raise ValueError("tie")
            low[k] = st[j]
        return low

    def asc(self, low, C):
        return [k for k in range(len(self.cells)) if low[k] == C and self.dim[k] > 0]

def rank_mod(A, p):
    A = A.copy() % p
    r = 0
    rows, cols = A.shape
    for c in range(cols):
        if r == rows:
            break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + nz[0]
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        col = A[:, c].copy(); col[r] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr):
            A[nzr] = (A[nzr] - np.outer(col[nzr], A[r])) % p
        r += 1
    return r

def poset_betti(S, els, upto, p=32003):
    """reduced Betti numbers b_0..b_upto over F_p of the order complex of the
    induced subposet els of the face poset of S (a down-closed set of cells)."""
    if not els:
        return None
    E = set(els)
    below = {k: [j for j in S.faces[k] if j in E] for k in els}
    chains = [[(k,) for k in els]]
    for d in range(1, upto + 2):
        nxt = [(j,) + c for c in chains[-1] for j in below[c[0]]]
        chains.append(nxt)
    idx = [{c: i for i, c in enumerate(ch)} for ch in chains]
    ranks = [0]
    for d in range(1, upto + 2):
        if not chains[d]:
            ranks.append(0); continue
        M = np.zeros((len(chains[d - 1]), len(chains[d])), dtype=np.int64)
        for j, c in enumerate(chains[d]):
            for t in range(len(c)):
                M[idx[d - 1][c[:t] + c[t + 1:]], j] += (-1) ** t
        ranks.append(rank_mod(M, p))
    ranks.append(0)
    b = []
    for d in range(upto + 1):
        v = len(chains[d]) - ranks[d] - ranks[d + 1]
        if d == 0:
            v -= 1
        b.append(v)
    return b
