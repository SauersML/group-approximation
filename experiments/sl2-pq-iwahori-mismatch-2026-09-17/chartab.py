"""Numerical character tables of small matrix groups over Z/M (Burnside's algorithm).

A group is given as an integer array `els` of shape (n, 4) holding the
entries (a, b, c, d) of 2x2 matrices mod M.  Identity must be els[0].
Characters are computed by simultaneous diagonalisation of the class
multiplication matrices and are checked against the orthogonality relations.
"""
import numpy as np


class MatGroup:
    def __init__(self, els, M):
        self.M = M
        self.els = np.asarray(els, dtype=np.int64) % M
        self.n = len(self.els)
        self.code = self._code(self.els)
        self.lookup = -np.ones(M ** 4, dtype=np.int64)
        self.lookup[self.code] = np.arange(self.n)
        assert (self.lookup[self.code] == np.arange(self.n)).all(), "duplicate elements"

    def _code(self, e):
        M = self.M
        return ((e[:, 0] * M + e[:, 1]) * M + e[:, 2]) * M + e[:, 3]

    def mul(self, X, Y):
        """Row-wise product of element arrays X, Y (entries mod M)."""
        a = X[:, 0] * Y[:, 0] + X[:, 1] * Y[:, 2]
        b = X[:, 0] * Y[:, 1] + X[:, 1] * Y[:, 3]
        c = X[:, 2] * Y[:, 0] + X[:, 3] * Y[:, 2]
        d = X[:, 2] * Y[:, 1] + X[:, 3] * Y[:, 3]
        return np.stack([a, b, c, d], axis=1) % self.M

    def inv(self, X):
        # determinant one: inverse is [[d,-b],[-c,a]]
        return np.stack([X[:, 3], -X[:, 1], -X[:, 2], X[:, 0]], axis=1) % self.M

    def index(self, X):
        idx = self.lookup[self._code(X % self.M)]
        assert (idx >= 0).all(), "element outside group"
        return idx

    def classes(self):
        n = self.n
        lab = np.arange(n)
        allg = self.els
        # conjugate by every element in blocks (exact class computation)
        cls = -np.ones(n, dtype=np.int64)
        reps = []
        for x in range(n):
            if cls[x] >= 0:
                continue
            X = np.repeat(self.els[x:x + 1], n, axis=0)
            orb = np.unique(self.index(self.mul(self.mul(allg, X), self.inv(allg))))
            cls[orb] = len(reps)
            reps.append(x)
        self.cls = cls
        self.reps = np.array(reps)
        self.r = len(reps)
        self.csize = np.bincount(cls, minlength=self.r)
        assert cls[0] == 0
        return self

    def character_table(self, seed=1):
        n, r = self.n, self.r
        allinv = self.inv(self.els)
        a = np.zeros((r, r, r))
        for k, zk in enumerate(self.reps):
            Z = np.repeat(self.els[zk:zk + 1], n, axis=0)
            ci = self.cls[self.index(self.mul(allinv, Z))]
            np.add.at(a, (self.cls, ci, k), 1.0)
        rng = np.random.default_rng(seed)
        coef = rng.standard_normal(r) + 1j * rng.standard_normal(r)
        Mx = np.tensordot(coef, a, axes=(0, 0))
        vals, vecs = np.linalg.eig(Mx)
        W = vecs / vecs[0:1, :]           # omega vectors, omega(identity) = 1
        tab = []
        for t in range(r):
            w = W[:, t]
            deg = np.sqrt(n / np.sum(np.abs(w) ** 2 / self.csize))
            tab.append(w * deg / self.csize)
        tab = np.array(tab)               # tab[chi, class]
        order = np.lexsort((np.round(np.abs(tab).sum(1), 6), np.round(tab[:, 0].real, 6)))
        tab = tab[order]
        # orthogonality check
        G = (tab * self.csize) @ tab.conj().T / n
        err = np.abs(G - np.eye(r)).max()
        assert err < 1e-6, f"orthogonality failure {err}"
        degs = np.round(tab[:, 0].real).astype(int)
        assert np.abs(tab[:, 0] - degs).max() < 1e-6 and (degs ** 2).sum() == n
        self.tab, self.degs = tab, degs
        return self
