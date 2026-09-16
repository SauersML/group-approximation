#!/usr/bin/env python3
"""Shared exact routines for the HC1 reflected-root-word experiments (2026-09-16).

Group (CCKW Theorem 1.3, G_HC^(1)_2(p)), conventions [x,y]=x^-1 y^-1 x y,
left-normed [x,y,z]=[[x,y],z]:

  Gamma_p = < a,b,c | a^p, b^p, c^p, [a,b,a], [a,b,b], [b,c,b], [b,c,c],
                      [a,c,a], [a,c,c,a], [a,c,c,c] >,
  r=[b,a], s=[b,c], w=(r s)^p.

Everything here is exact integer arithmetic modulo a prime q (numpy int64,
entries reduced after every product; q < 2^15 so products never overflow).
Words are lists of (generator index, exponent +-1); generators 0=a, 1=b, 2=c.
"""
import numpy as np

A_, B_, C_ = 0, 1, 2


def inv_word(u):
    return [(g, -e) for (g, e) in reversed(u)]


def comm(u, v):
    return inv_word(u) + inv_word(v) + u + v


def lcomm(*ws):
    out = ws[0]
    for v in ws[1:]:
        out = comm(out, v)
    return out


def gen(g):
    return [(g, 1)]


def relators(p):
    a, b, c = gen(A_), gen(B_), gen(C_)
    return [
        ("a^p", a * p), ("b^p", b * p), ("c^p", c * p),
        ("[a,b,a]", lcomm(a, b, a)), ("[a,b,b]", lcomm(a, b, b)),
        ("[b,c,b]", lcomm(b, c, b)), ("[b,c,c]", lcomm(b, c, c)),
        ("[a,c,a]", lcomm(a, c, a)), ("[a,c,c,a]", lcomm(a, c, c, a)),
        ("[a,c,c,c]", lcomm(a, c, c, c)),
    ]


def root_word(p):
    a, b, c = gen(A_), gen(B_), gen(C_)
    rs = comm(b, a) + comm(b, c)
    return rs * p


def rs_word():
    a, b, c = gen(A_), gen(B_), gen(C_)
    return comm(b, a) + comm(b, c)


def mat_inv_mod(M, q):
    n = M.shape[0]
    W = np.concatenate([M % q, np.eye(n, dtype=np.int64)], axis=1)
    for col in range(n):
        piv = None
        for r in range(col, n):
            if W[r, col] % q:
                piv = r
                break
        if piv is None:
            raise ValueError("singular matrix")
        if piv != col:
            W[[col, piv]] = W[[piv, col]]
        W[col] = (W[col] * pow(int(W[col, col]), q - 2, q)) % q
        f = W[:, col].copy()
        f[col] = 0
        nz = np.nonzero(f)[0]
        if len(nz):
            W[nz] = (W[nz] - np.outer(f[nz], W[col])) % q
    return W[:, n:] % q


class Rep:
    """A homomorphism from the free group on a,b,c to GL_n(F_q)."""

    def __init__(self, mats, q):
        self.q = q
        self.m = [np.array(M, dtype=np.int64) % q for M in mats]
        self.n = self.m[0].shape[0]
        self.mi = [mat_inv_mod(M, q) for M in self.m]

    def letter(self, g, e):
        return self.m[g] if e == 1 else self.mi[g]

    def eval(self, word):
        P = np.eye(self.n, dtype=np.int64)
        for (g, e) in word:
            P = (P @ self.letter(g, e)) % self.q
        return P

    def is_identity(self, word):
        return bool(np.array_equal(self.eval(word), np.eye(self.n, dtype=np.int64)))

    def check_relators(self, p):
        return {name: self.is_identity(u) for (name, u) in relators(p)}

    def fox(self, word):
        """Return (rho(word), [C_a, C_b, C_c]) with delta(word) = sum_x C_x delta(x)
        for every cocycle delta: F -> F_q^n of this action (left module)."""
        q, n = self.q, self.n
        P = np.eye(n, dtype=np.int64)
        C = [np.zeros((n, n), dtype=np.int64) for _ in range(3)]
        for (g, e) in word:
            if e == 1:
                C[g] = (C[g] + P) % q
            else:
                C[g] = (C[g] - P @ self.mi[g]) % q
            P = (P @ self.letter(g, e)) % q
        return P, C


def rref_nullspace(M, q):
    """Basis (as columns) of the right nullspace of M over F_q."""
    M = M.copy() % q
    rows, cols = M.shape
    pivcols = []
    r = 0
    for col in range(cols):
        if r >= rows:
            break
        piv = None
        nzr = np.nonzero(M[r:, col])[0]
        if len(nzr) == 0:
            continue
        piv = r + nzr[0]
        if piv != r:
            M[[r, piv]] = M[[piv, r]]
        M[r] = (M[r] * pow(int(M[r, col]), q - 2, q)) % q
        f = M[:, col].copy()
        f[r] = 0
        nz = np.nonzero(f)[0]
        if len(nz):
            M[nz] = (M[nz] - np.outer(f[nz], M[r])) % q
        pivcols.append(col)
        r += 1
    free = [c for c in range(cols) if c not in set(pivcols)]
    N = np.zeros((cols, len(free)), dtype=np.int64)
    for j, fc in enumerate(free):
        N[fc, j] = 1
        for i, pc in enumerate(pivcols):
            N[pc, j] = (-M[i, fc]) % q
    return N


def rank_mod(M, q):
    M = M.copy() % q
    rows, cols = M.shape
    r = 0
    for col in range(cols):
        if r >= rows:
            break
        nzr = np.nonzero(M[r:, col])[0]
        if len(nzr) == 0:
            continue
        piv = r + nzr[0]
        if piv != r:
            M[[r, piv]] = M[[piv, r]]
        M[r] = (M[r] * pow(int(M[r, col]), q - 2, q)) % q
        f = M[:, col].copy()
        f[r] = 0
        nz = np.nonzero(f)[0]
        if len(nz):
            M[nz] = (M[nz] - np.outer(f[nz], M[r])) % q
        r += 1
    return r


def cocycle_space(rep, p):
    """Z^1(Gamma_p; F_q^n) as a (3n x k) basis matrix, columns = (d_a,d_b,d_c)."""
    blocks = []
    for (_, u) in relators(p):
        P, C = rep.fox(u)
        blocks.append(np.concatenate(C, axis=1))
    M = np.concatenate(blocks, axis=0)
    return rref_nullspace(M, rep.q)


def root_word_translation_rank(rep, p):
    """Rank of the linear map Z^1 -> F_q^n, delta -> delta(w_p).  Positive rank
    means the affine lift F_q^n x| rho(Gamma) is a finite image in which w_p
    survives (when rho(w_p)=1)."""
    K = cocycle_space(rep, p)
    P, C = rep.fox(root_word(p))
    L = np.concatenate(C, axis=1)
    img = (L @ K) % rep.q
    return K.shape[1], rank_mod(img, rep.q), K, L, P


def affine_lift(rep, delta):
    """Matrices (n+1)x(n+1): g -> [[rho(g), delta(g)],[0,1]] for generators."""
    n, q = rep.n, rep.q
    out = []
    for g in range(3):
        M = np.zeros((n + 1, n + 1), dtype=np.int64)
        M[:n, :n] = rep.m[g]
        M[:n, n] = delta[g * n:(g + 1) * n] % q
        M[n, n] = 1
        out.append(M)
    return out


def monomials(n, m):
    import itertools
    return [e for e in itertools.product(range(m + 1), repeat=n) if sum(e) == m]


def sym_power(g, m, q):
    """Matrix of Sym^m(g) on degree-m monomials, where g x_j = sum_i g[i,j] x_i."""
    n = g.shape[0]
    mons = monomials(n, m)
    idx = {e: i for i, e in enumerate(mons)}
    S = np.zeros((len(mons), len(mons)), dtype=np.int64)
    lin = [{tuple(1 if t == i else 0 for t in range(n)): int(g[i, j]) % q
            for i in range(n) if g[i, j] % q} for j in range(n)]
    for e in mons:
        poly = {tuple([0] * n): 1}
        for j in range(n):
            for _ in range(e[j]):
                new = {}
                for mon, cf in poly.items():
                    for mon2, cf2 in lin[j].items():
                        mm = tuple(x + y for x, y in zip(mon, mon2))
                        new[mm] = (new.get(mm, 0) + cf * cf2) % q
                poly = {k: v for k, v in new.items() if v}
        for mon, cf in poly.items():
            S[idx[mon], idx[e]] = cf
    return S


def normalize(v, p):
    for x in v:
        if x % p:
            inv = pow(int(x), p - 2, p)
            return tuple(int(y * inv) % p for y in v)
    return None


def perm_rep(mats, points, p, ell, kind):
    """Permutation module over F_ell for the projective action of matrices over
    F_p on points (kind='pt', v -> g v) or hyperplanes (kind='line', phi -> phi g^-1)."""
    index = {pt: i for i, pt in enumerate(points)}
    out = []
    for g in mats:
        g = np.array(g, dtype=np.int64) % p
        gi = mat_inv_mod(g, p)
        M = np.zeros((len(points), len(points)), dtype=np.int64)
        for pt in points:
            if kind == "pt":
                img = normalize(tuple(int(x) % p for x in g @ np.array(pt)), p)
            else:
                img = normalize(tuple(int(x) % p for x in np.array(pt) @ gi), p)
            M[index[img], index[pt]] = 1
        out.append(M)
    return Rep(out, ell)
