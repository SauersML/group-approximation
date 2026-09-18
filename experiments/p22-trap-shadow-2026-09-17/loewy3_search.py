#!/usr/bin/env python3
"""Loewy-length-three linear models of the trap-relator group Gamma.

W = W2 + W1 + W0 over GF(2), each layer W_i = X_i (x) Y_i with the left Levi
generators (as, at, c) acting by L_i (x) 1 and the right Levi generators
(b1, bs, bt) by 1 (x) R_i, so left and right commute.  The unipotent
generator is
        u = [[1, alpha, gamma], [0, 1, beta], [0, 0, 1]].
All derived words of trap_group.DERIVED are block unitriangular.

Degree one: the alpha- and beta-blocks of the trap relations are the linear
trap, a linear system A (resp. B) in alpha (resp. beta).
Degree two: for a FIXED alpha in A, every gamma-block (of every relation,
of u^2, and of h) is linear in the pair (beta, gamma_u) jointly, because the
only quadratic terms are alpha-beta products.  So "is there a model with
gamma_h != 0" is decided exactly, for fixed alpha, by linear algebra: the
map (beta, gamma_u) -> gamma_h must be nonzero on the kernel of the map
(beta, gamma_u) -> (all gamma-block discrepancies).

Usage: loewy3_search.py SEED TRIALS [extra]
Any hit is re-verified by full matrix evaluation of every relation.
"""
import sys

import numpy as np

import gf2
import trap_group as TG

LEFT = ["as", "at", "c"]
RIGHT = ["b1", "bs", "bt"]


def rand_inv(k, rng):
    """Random involution in GL_k(F_2) (conjugate of a random Jordan form)."""
    while True:
        P = rng.integers(0, 2, (k, k)).astype(np.uint8)
        if gf2.rank(P) == k:
            break
    J = np.eye(k, dtype=np.uint8)
    nblocks = rng.integers(0, k // 2 + 1)
    for b in range(nblocks):
        J[2 * b, 2 * b + 1] = 1
    Pinv = inverse(P)
    return gf2.mm(P, J, Pinv)


def inverse(P):
    k = P.shape[0]
    aug = np.concatenate([P, np.eye(k, dtype=np.uint8)], axis=1)
    R, piv = gf2.rref(aug)
    assert piv[:k] == list(range(k))
    return R[:, k:]


def kron(A, B):
    return (np.kron(A.astype(np.int64), B.astype(np.int64)) % 2).astype(np.uint8)


class Model:
    """Layers: list of three (Ldict, Rdict), index 0 = W2 (top), 2 = W0."""

    def __init__(self, layers):
        self.layers = layers
        self.dims = []
        self.levi = {g: [] for g in LEFT + RIGHT}
        for Ld, Rd in layers:
            a = Ld["as"].shape[0]
            b = Rd["b1"].shape[0]
            self.dims.append(a * b)
            for g in LEFT:
                self.levi[g].append(kron(Ld[g], np.eye(b, dtype=np.uint8)))
            for g in RIGHT:
                self.levi[g].append(kron(np.eye(a, dtype=np.uint8), Rd[g]))
        d2, d1, d0 = self.dims
        self.n = d2 + d1 + d0
        self.off = [0, d2, d2 + d1, self.n]
        self.G = {}
        for g in LEFT + RIGHT:
            M = np.zeros((self.n, self.n), dtype=np.uint8)
            for i in range(3):
                s, e = self.off[i], self.off[i + 1]
                M[s:e, s:e] = self.levi[g][i]
            self.G[g] = M

    def block(self, M, i, j):
        return M[self.off[i]:self.off[i + 1], self.off[j]:self.off[j + 1]]

    def unip(self, alpha, beta, gamma):
        M = np.eye(self.n, dtype=np.uint8)
        o = self.off
        M[o[0]:o[1], o[1]:o[2]] = alpha
        M[o[1]:o[2], o[2]:o[3]] = beta
        M[o[0]:o[1], o[2]:o[3]] = gamma
        return M

    def evaluate(self, U, rels):
        val = dict(self.G)
        val["u"] = U
        for name, word in TG.DERIVED:
            val[name] = gf2.mm(*[val[g] for g in word])
        out = []
        for name, lhs, rhs in rels:
            out.append((name, gf2.mm(*[val[g] for g in lhs]),
                        gf2.mm(*[val[g] for g in rhs])))
        return val, out


def disc_vector(model, U, rels, bi, bj):
    """Concatenated (bi,bj)-blocks of lhs+rhs over all relations, and of u^2+1."""
    val, out = model.evaluate(U, rels)
    parts = [(model.block(l, bi, bj) ^ model.block(r, bi, bj)).ravel() for _, l, r in out]
    uu = gf2.mm(U, U)
    eye = np.eye(model.n, dtype=np.uint8)
    parts.append((model.block(uu, bi, bj) ^ model.block(eye, bi, bj)).ravel())
    return np.concatenate(parts), val


def zeros(a, b):
    return np.zeros((a, b), dtype=np.uint8)


def degree_one(model, rels):
    d2, d1, d0 = model.dims
    colsA, colsB, hA, hB = [], [], [], []
    for i in range(d2):
        for j in range(d1):
            a = zeros(d2, d1)
            a[i, j] = 1
            v, val = disc_vector(model, model.unip(a, zeros(d1, d0), zeros(d2, d0)), rels, 0, 1)
            colsA.append(v)
            hA.append(model.block(val["h"], 0, 1).ravel())
    for i in range(d1):
        for j in range(d0):
            b = zeros(d1, d0)
            b[i, j] = 1
            v, val = disc_vector(model, model.unip(zeros(d2, d1), b, zeros(d2, d0)), rels, 1, 2)
            colsB.append(v)
            hB.append(model.block(val["h"], 1, 2).ravel())
    MA = np.array(colsA, dtype=np.uint8).T
    MB = np.array(colsB, dtype=np.uint8).T
    NA = gf2.nullspace(MA)
    NB = gf2.nullspace(MB)
    HA = np.array(hA, dtype=np.uint8).T
    HB = np.array(hB, dtype=np.uint8).T
    trapA = all(not gf2.mm(HA, x.reshape(-1, 1)).any() for x in NA)
    trapB = all(not gf2.mm(HB, x.reshape(-1, 1)).any() for x in NB)
    return NA, NB, trapA, trapB


def degree_two(model, rels, alpha, NB):
    """For fixed alpha: is there (beta in span NB, gamma_u) with every
    gamma-block discrepancy zero and gamma_h != 0?  Exact linear algebra."""
    d2, d1, d0 = model.dims
    zb, zg = zeros(d1, d0), zeros(d2, d0)
    cols, hcols, pts = [], [], []
    for x in NB:
        pts.append((x.reshape(d1, d0).astype(np.uint8), zg))
    for i in range(d2):
        for j in range(d0):
            g = zg.copy()
            g[i, j] = 1
            pts.append((zb, g))
    for b, g in pts:
        v, val = disc_vector(model, model.unip(alpha, b, g), rels, 0, 2)
        cols.append(v)
        hcols.append(model.block(val["h"], 0, 2).ravel())
    M = np.array(cols, dtype=np.uint8).T
    H = np.array(hcols, dtype=np.uint8).T
    K = gf2.nullspace(M)
    for z in K:
        if gf2.mm(H, z.reshape(-1, 1)).any():
            beta = zeros(d1, d0)
            for k in range(len(NB)):
                if z[k]:
                    beta ^= pts[k][0]
            gamma = z[len(NB):].reshape(d2, d0).astype(np.uint8)
            return True, beta, gamma, len(K)
    return False, None, None, len(K)


def verify(model, U, rels):
    val, out = model.evaluate(U, rels)
    eye = np.eye(model.n, dtype=np.uint8)
    ok = all(np.array_equal(l, r) for _, l, r in out)
    ok = ok and np.array_equal(gf2.mm(U, U), eye)
    for g in LEFT + RIGHT:
        ok = ok and np.array_equal(gf2.mm(model.G[g], model.G[g]), eye)
    for x in LEFT:
        for y in RIGHT:
            ok = ok and np.array_equal(gf2.mm(model.G[x], model.G[y]),
                                       gf2.mm(model.G[y], model.G[x]))
    head = not np.array_equal(val["h"], eye)
    return ok, head, val


def search(model, rels, rng, alpha_samples=64):
    NA, NB, tA, tB = degree_one(model, rels)
    info = {"dimA": len(NA), "dimB": len(NB), "trapA": tA, "trapB": tB}
    if len(NA) == 0 or len(NB) == 0:
        return None, info
    alphas = []
    if len(NA) <= 6:
        for mask in range(1, 2 ** len(NA)):
            a = np.zeros(NA.shape[1], dtype=np.uint8)
            for k in range(len(NA)):
                if (mask >> k) & 1:
                    a ^= NA[k]
            alphas.append(a)
    else:
        alphas = list(NA)
        for _ in range(alpha_samples):
            c = rng.integers(0, 2, len(NA))
            alphas.append((c.astype(np.int64) @ NA.astype(np.int64) % 2).astype(np.uint8))
    d2, d1, _ = model.dims
    for a in alphas:
        alpha = a.reshape(d2, d1).astype(np.uint8)
        found, beta, gamma, kdim = degree_two(model, rels, alpha, NB)
        if found:
            U = model.unip(alpha, beta, gamma)
            ok, head, _ = verify(model, U, rels)
            info["verified"] = ok
            info["head"] = head
            return (alpha, beta, gamma, U), info
    return None, info


def random_layer(a, b, rng):
    Ld = {g: rand_inv(a, rng) for g in LEFT}
    Rd = {g: rand_inv(b, rng) for g in RIGHT}
    return Ld, Rd


def main():
    seed = int(sys.argv[1])
    trials = int(sys.argv[2])
    extra = len(sys.argv) > 3 and sys.argv[3] == "extra"
    rels = TG.TRAP_RELS + (TG.EXTRA_RELS if extra else [])
    rng = np.random.default_rng(seed)
    stats = {"trials": 0, "nontrivialA_B": 0, "hits": 0}
    for t in range(trials):
        shapes = [(int(rng.integers(1, 4)), int(rng.integers(1, 4))) for _ in range(3)]
        layers = [random_layer(a, b, rng) for a, b in shapes]
        model = Model(layers)
        res, info = search(model, rels, rng)
        stats["trials"] += 1
        assert info["trapA"] and info["trapB"], "linear trap violated?!"
        if info["dimA"] and info["dimB"]:
            stats["nontrivialA_B"] += 1
        if res is not None:
            stats["hits"] += 1
            print("HIT trial", t, "shapes", shapes, info)
            for g in LEFT + RIGHT:
                print(" ", g, model.G[g].tolist())
            print("  u", res[3].tolist())
            break
    print("extra" if extra else "trap-only", stats)


if __name__ == "__main__":
    main()
