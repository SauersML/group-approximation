#!/usr/bin/env python3
"""GF(q) (q <= ~4096) with full add/mul tables, and table-driven rank.
Elements are ints 0..q-1; 0 = zero, 1 = one."""
import numpy as np
from gfq import GF


class GFT:
    def __init__(self, p, k):
        base = GF(p, k)
        self.p, self.k, self.q = p, k, base.q
        q = self.q
        a = np.arange(q)
        self.add = np.zeros((q, q), dtype=np.int32)
        for x in range(q):
            self.add[x] = base.add(np.full(q, x), a)
        self.mul = np.zeros((q, q), dtype=np.int32)
        for x in range(q):
            self.mul[x] = base.mul(np.full(q, x), a)
        self.neg = np.array([int(base.neg(np.array([x]))[0]) for x in range(q)], dtype=np.int32)
        self.inv = np.zeros(q, dtype=np.int32)
        for x in range(1, q):
            self.inv[x] = base.inv(x)
        self.exp = base.exp
        self.log = base.log

    def pow(self, x, m):
        return int(self.exp[(int(self.log[x]) * m) % (self.q - 1)])

    def rank(self, M):
        M = np.array(M, dtype=np.int32)
        rows, cols = M.shape
        r = 0
        for c in range(cols):
            if r == rows:
                break
            piv = np.nonzero(M[r:, c])[0]
            if len(piv) == 0:
                continue
            i = r + piv[0]
            if i != r:
                M[[r, i]] = M[[i, r]]
            M[r] = self.mul[self.inv[M[r, c]], M[r]]
            col = M[:, c].copy()
            col[r] = 0
            nz = np.nonzero(col)[0]
            if len(nz):
                negc = self.neg[col[nz]]
                prod = self.mul[negc[:, None], M[r][None, :]]
                M[nz] = self.add[M[nz], prod]
            r += 1
        return r


class PrimeField:
    """GF(P) for a large prime P, same interface."""
    def __init__(self, P=1000003):
        self.p = self.q = P

    def pow(self, x, m):
        return pow(x, m % (self.p - 1), self.p)

    def rank(self, M):
        from twisted_alexander import rank_mod_p
        return rank_mod_p(M, self.p)
