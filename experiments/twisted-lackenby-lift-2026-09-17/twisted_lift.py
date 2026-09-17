#!/usr/bin/env python3
"""Twisted Lackenby lifting: numerical check.

Setting.  K = presentation complex of <X|R>, pi = pi_1(K).  M = F_p^d with a
left action rho: pi -> GL_d(F_p) through a finite quotient.  U = u scalar
1-cocycles (c_i: X -> F_p, zero on relators).  C = h twisted derivations
(xi_j: X -> M, xi_j(w)=0 on relators) independent modulo coboundaries.

Cover K~ for A' = ker(pi -> M^h x| Q), g -> (rho(g), xi_1(g),...,xi_h(g)).
Vertices of K~ = states (rho(g), xi(g)); edge (g,s): g -> g s.

Cochains Y_ij(g,s) = c_i(s) * xi_j(g) in M (M is trivial on A', so every
coordinate of an M-valued cocycle on K~ is an F_p-cocycle).

Measured:  z   = dim of {a in F_p^(u h): sum a_ij Y_ij is a cocycle}
           cls = number of independent classes in H^1(K~;F_p) spanned by the
                 coordinates of those cocycles (all supported over supp U).
Predicted: z >= u h - r d  (twisted Lemma 5.7: deck translates of a 2-cell
           give q(d)-translates of the same M-valued evaluation), and the
           question is how far cls falls below z/d.
"""
import itertools, sys
import numpy as np


def rank_mod_p(A, p):
    A = np.array(A, dtype=np.int64) % p
    if A.size == 0:
        return 0
    A = A.copy()
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        if r == rows:
            break
        piv = np.nonzero(A[r:, c])[0]
        if len(piv) == 0:
            continue
        k = r + piv[0]
        if k != r:
            A[[r, k]] = A[[k, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        nz = np.nonzero(A[:, c])[0]
        for k in nz:
            if k != r:
                A[k] = (A[k] - A[k, c] * A[r]) % p
        r += 1
    return r


def nullspace_mod_p(A, p):
    """Basis of {a : a A = 0} for row vector a (left nullspace)."""
    A = np.array(A, dtype=np.int64) % p
    n = A.shape[0]
    Aug = np.concatenate([A, np.eye(n, dtype=np.int64)], axis=1)
    m = A.shape[1]
    rows = n
    r = 0
    for c in range(m):
        if r == rows:
            break
        piv = np.nonzero(Aug[r:, c])[0]
        if len(piv) == 0:
            continue
        k = r + piv[0]
        if k != r:
            Aug[[r, k]] = Aug[[k, r]]
        inv = pow(int(Aug[r, c]), p - 2, p)
        Aug[r] = (Aug[r] * inv) % p
        for k in np.nonzero(Aug[:, c])[0]:
            if k != r:
                Aug[k] = (Aug[k] - Aug[k, c] * Aug[r]) % p
        r += 1
    return Aug[r:, m:]


def matinv_mod_p(Mx, p):
    d = Mx.shape[0]
    Aug = np.concatenate([Mx % p, np.eye(d, dtype=np.int64)], axis=1)
    for c in range(d):
        k = c + np.nonzero(Aug[c:, c])[0][0]
        Aug[[c, k]] = Aug[[k, c]]
        Aug[c] = Aug[c] * pow(int(Aug[c, c]), p - 2, p) % p
        for k in range(d):
            if k != c and Aug[k, c]:
                Aug[k] = (Aug[k] - Aug[k, c] * Aug[c]) % p
    return Aug[:, d:]


class Setup:
    def __init__(self, p, ngen, relators, rho):
        self.p, self.ngen, self.rel = p, ngen, relators
        self.rho = [np.array(m, dtype=np.int64) % p for m in rho]
        self.rhoinv = [matinv_mod_p(m, p) for m in self.rho]
        self.d = self.rho[0].shape[0]

    # --- scalar cocycles and derivations on K ---
    def scalar_cocycles(self):
        p = self.p
        rows = []
        for w in self.rel:
            v = [0] * self.ngen
            for s, e in w:
                v[s] += e
            rows.append(v)
        if not rows:
            return np.eye(self.ngen, dtype=np.int64)
        # a in F_p^X with rows . a = 0  -> left nullspace of transpose
        return nullspace_mod_p(np.array(rows).T, p)

    def fox_word(self, w):
        """Linear map (xi(s))_s -> xi(w) as d x (d*ngen) matrix, and rho(w)."""
        p, d = self.p, self.d
        L = np.zeros((d, d * self.ngen), dtype=np.int64)
        R = np.eye(d, dtype=np.int64)
        for s, e in w:
            if e == 1:
                L[:, d * s:d * (s + 1)] = (L[:, d * s:d * (s + 1)] + R) % p
                R = R @ self.rho[s] % p
            else:
                R = R @ self.rhoinv[s] % p
                L[:, d * s:d * (s + 1)] = (L[:, d * s:d * (s + 1)] - R) % p
        return L, R

    def derivations_mod_coboundaries(self):
        p, d = self.p, self.d
        rows = [self.fox_word(w)[0] for w in self.rel]
        if rows:
            Z = nullspace_mod_p(np.concatenate(rows, axis=0).T, p)  # derivation vectors
        else:
            Z = np.eye(d * self.ngen, dtype=np.int64)
        # coboundaries: xi(s) = rho(s) m - m
        B = []
        for k in range(d):
            m = np.zeros(d, dtype=np.int64); m[k] = 1
            B.append(np.concatenate([(self.rho[s] @ m - m) % p for s in range(self.ngen)]))
        B = np.array(B)
        rB = rank_mod_p(B, p)
        basis = [b for b in B]
        cur = rB
        chosen = []
        for z in Z:
            if rank_mod_p(np.array(basis + [z]), p) > cur:
                basis.append(z); cur += 1; chosen.append(z)
        return np.array(chosen, dtype=np.int64).reshape(-1, d * self.ngen)

    # --- cover ---
    def build_cover(self, C, limit=200000):
        p, d = self.p, self.d
        h = len(C)
        xis = [[C[j][d * s:d * (s + 1)] for s in range(self.ngen)] for j in range(h)]
        start = (tuple(np.eye(d, dtype=np.int64).flatten()), tuple([0] * (d * h)))
        index = {start: 0}
        states = [start]
        edges = []  # (v, s, w)
        i = 0
        while i < len(states):
            q, x = states[i]
            Qm = np.array(q, dtype=np.int64).reshape(d, d)
            X = np.array(x, dtype=np.int64).reshape(h, d) if h else np.zeros((0, d), dtype=np.int64)
            for s in range(self.ngen):
                nq = tuple((Qm @ self.rho[s] % p).flatten())
                nx = tuple(((X + np.array([Qm @ xis[j][s] for j in range(h)]).reshape(h, d)) % p).flatten()) if h else tuple()
                key = (nq, nx)
                if key not in index:
                    index[key] = len(states); states.append(key)
                    if len(states) > limit:
                        raise RuntimeError("cover too large")
                edges.append((i, s, index[key]))
            i += 1
        return states, index, edges

    def run(self, U, C):
        p, d = self.p, self.d
        u, h = len(U), len(C)
        states, index, edges = self.build_cover(C)
        V, E = len(states), len(edges)
        eidx = {(a, s): k for k, (a, s, b) in enumerate(edges)}
        self._predmap = {(b, s): a for (a, s, b) in edges}
        # Y_ij as M-valued cochains: array (u*h, E, d)
        Y = np.zeros((u * h, E, d), dtype=np.int64)
        for k, (a, s, b) in enumerate(edges):
            xa = np.array(states[a][1], dtype=np.int64).reshape(h, d)
            for i_ in range(u):
                if U[i_][s] % p:
                    for j in range(h):
                        Y[i_ * h + j, k] = U[i_][s] * xa[j] % p
        # 2-cells at every vertex
        cond = []
        for a in range(V):
            for w in self.rel:
                ev = np.zeros((u * h, d), dtype=np.int64)
                cur = a
                for s, e in w:
                    if e == 1:
                        k = eidx[(cur, s)]
                        ev = ev + Y[:, k]
                        cur = edges[k][2]
                    else:
                        # find edge (prev, s) -> cur
                        prev = self._pred(cur, s, states, index)
                        k = eidx[(prev, s)]
                        ev = ev - Y[:, k]
                        cur = prev
                cond.append(ev % p)
        if cond:
            Cm = np.concatenate(cond, axis=1)  # (u*h, V*|R|*d)
            Z = nullspace_mod_p(Cm, p)
        else:
            Z = np.eye(u * h, dtype=np.int64)
        z = len(Z)
        # coordinate cochains
        coords = []
        for a_ in Z:
            Ya = np.tensordot(a_, Y, axes=(0, 0)) % p  # (E, d)
            for k in range(d):
                coords.append(Ya[:, k])
        B = np.zeros((V, E), dtype=np.int64)
        for k, (a, s, b) in enumerate(edges):
            B[b, k] += 1; B[a, k] -= 1
        B %= p
        rB = rank_mod_p(B, p)
        cls = rank_mod_p(np.concatenate([B] + ([np.array(coords)] if coords else []), axis=0), p) - rB
        return dict(V=V, E=E, u=u, h=h, d=d, r=len(self.rel), z=z, cls=cls,
                    naive=u * h - len(self.rel) * d)

    def _pred(self, cur, s, states, index):
        return self._predmap[(cur, s)]


def run_case(name, p, ngen, rel, rho, Usel=None, Csel=None, Uexplicit=None):
    S = Setup(p, ngen, rel, rho)
    U = S.scalar_cocycles()
    if Usel is not None:
        U = np.array([U[i] for i in Usel])
    if Uexplicit is not None:
        U = np.array(Uexplicit, dtype=np.int64)
    C = S.derivations_mod_coboundaries()
    if Csel is not None:
        C = np.array([C[j] for j in Csel])
    res = S.run(U, C)
    print(name, res, flush=True)
    return res


if __name__ == "__main__":
    pass
