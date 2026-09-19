#!/usr/bin/env python3
"""Depth scan of class-two tensor models of Gamma_trap (+ EXTRA_RELS + (C1),(C2)
at right-orbit depth <= k) over general ring Levi modules.

Model (same group law as the w10-ptl-follow verify_hit.py, re-implemented):
  W = M_2(A_1) + ... + M_2(A_r),  A_i = F_2[x]/(p_i),  S -> a_i, T -> a_i^{-1}
  (a_i any unit of A_i), left EL_2 by Y -> aY, right by Y -> Yb,
  N_W = W x (W (x) W), (w,z)(w',z') = (w+w', z+z'+w w'^T), G0 acts (Aw, AzA^T),
  u = (v, c_u), v = sum of E_11, c_u random.  K = G0-span of relator differences.
  Head survives iff the C-part of h = u.ust is not in K.
Usage:
  c2scan.py single DEGMAX DEPTH SEEDS      all p (p(0)=1, deg<=DEGMAX), all units a
  c2scan.py pair DEGMAX DEPTH SEEDS        direct sums of two such modules (S -> x)
  c2scan.py one P A DEPTH SEEDS            one module, p and a given as ints
"""
import itertools
import random
import sys

import numpy as np

from words import DERIVED, TRAP_RELS, INVOL_RELS, EXTRA_RELS, LEFT, RIGHT


def pmod(a, p):
    dp = p.bit_length() - 1
    while a and a.bit_length() - 1 >= dp:
        a ^= p << (a.bit_length() - 1 - dp)
    return a


def pmul(a, b, p):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
    return pmod(r, p)


def units(p):
    k = p.bit_length() - 1
    return [a for a in range(1, 1 << k) if any(pmul(a, b, p) == 1 for b in range(1, 1 << k))]


def inv(a, p):
    k = p.bit_length() - 1
    for b in range(1, 1 << k):
        if pmul(a, b, p) == 1:
            return b
    raise ValueError


def ring_module(p, xs):
    k = p.bit_length() - 1
    n = 4 * k
    xt = inv(xs, p)

    def vec(Y):
        v = np.zeros(n, np.uint8)
        for e in range(4):
            for j in range(k):
                v[e * k + j] = Y[e] >> j & 1
        return v

    def mat(f):
        M = np.zeros((n, n), np.uint8)
        for e in range(4):
            for j in range(k):
                Y = [0, 0, 0, 0]
                Y[e] = 1 << j
                M[:, e * k + j] = vec(f(Y))
        return M

    def m2(a, Y):  # a*Y
        a11, a12, a21, a22 = a
        y11, y12, y21, y22 = Y
        return (pmul(a11, y11, p) ^ pmul(a12, y21, p), pmul(a11, y12, p) ^ pmul(a12, y22, p),
                pmul(a21, y11, p) ^ pmul(a22, y21, p), pmul(a21, y12, p) ^ pmul(a22, y22, p))

    L = lambda a: mat(lambda Y: m2(a, Y))
    R = lambda b: mat(lambda Y: m2(Y, b))
    mats = {"as": L((1, xs, 0, 1)), "at": L((1, xt, 0, 1)), "c": L((1, 0, 1, 1)),
            "b1": R((1, 1, 0, 1)), "bs": R((1, 0, xs, 1)), "bt": R((1, 0, xt, 1))}
    return mats, vec((1, 0, 0, 0))


def direct_sum(parts):
    mats = {}
    for g in parts[0][0]:
        bl = [P[0][g] for P in parts]
        n = sum(B.shape[0] for B in bl)
        M = np.zeros((n, n), np.uint8)
        o = 0
        for B in bl:
            M[o:o + B.shape[0], o:o + B.shape[0]] = B
            o += B.shape[0]
        mats[g] = M
    return mats, np.concatenate([P[1] for P in parts])


def mm(A, B):
    return (A.astype(np.int64) @ B.astype(np.int64) % 2).astype(np.uint8)


def mul(X, Y):
    (w, z, A), (w2, z2, B) = X, Y
    w2a = mm(A, w2.reshape(-1, 1)).reshape(-1)
    return (w ^ w2a, z ^ mm(mm(A, z2), A.T) ^ np.outer(w, w2a).astype(np.uint8), mm(A, B))


def word(vals, wd, n):
    acc = (np.zeros(n, np.uint8), np.zeros((n, n), np.uint8), np.eye(n, dtype=np.uint8))
    for g in wd:
        acc = mul(acc, vals[g])
    return acc


def toint(z):
    return int.from_bytes(np.packbits(z.reshape(-1), bitorder="little").tobytes(), "little")


def fromint(x, n):
    b = np.frombuffer(x.to_bytes((n * n + 7) // 8, "little"), np.uint8)
    return np.unpackbits(b, bitorder="little")[: n * n].reshape(n, n)


class Basis:
    def __init__(self):
        self.piv = {}

    def red(self, v):
        while v:
            p = v.bit_length() - 1
            if p not in self.piv:
                return v
            v ^= self.piv[p]
        return 0

    def add(self, v):
        v = self.red(v)
        if v:
            self.piv[v.bit_length() - 1] = v
        return v


def closure(mats, gens, n):
    K = Basis()
    queue = [g for g in gens if g]
    while queue:
        x = K.add(queue.pop())
        if not x:
            continue
        z = fromint(x, n)
        for A in mats.values():
            y = toint(mm(mm(A, z), A.T))
            if K.red(y):
                queue.append(y)
    return K


def build(mats, v, cu):
    n = v.shape[0]
    zw, zz = np.zeros(n, np.uint8), np.zeros((n, n), np.uint8)
    vals = {g: (zw, zz, mats[g]) for g in LEFT + RIGHT}
    vals["u"] = (v.copy(), cu, np.eye(n, dtype=np.uint8))
    for name, wd in DERIVED:
        vals[name] = word(vals, wd, n)
    return vals


def rel_diffs(vals, rels, n):
    out = []
    for name, l, r in rels:
        X, Y = word(vals, l, n), word(vals, r, n)
        if (X[0] != Y[0]).any() or (X[2] != Y[2]).any():
            return None  # fails already at the W / G0 level
        out.append(toint(X[1] ^ Y[1]))
    return out


def orbit_rel_diffs(vals, n, depth):
    """(C1) [bzb, czc] = 1 and (C2) [bz'b, az'a] = 1 (z' = d_c z) for right words
    z = d_(b_1)...d_(b_j) u, j <= depth; all true in P_{2,2}(J)."""
    def w(names, X):
        env = dict(vals)
        env["x"] = X
        return word(env, names, n)

    level, out = [vals["u"]], []
    for j in range(depth + 1):
        nxt = []
        for z in level:
            zc = w(["x", "c", "x", "c"], z)
            pairs = [(w([b, "x", b], z), w(["c", "x", "c"], z)) for b in RIGHT]
            pairs += [(w([b, "x", b], zc), w([a, "x", a], zc)) for b in RIGHT for a in ["as", "at"]]
            for X, Y in pairs:
                XY, YX = mul(X, Y), mul(Y, X)
                out.append(toint(XY[1] ^ YX[1]))
            nxt += [w(["x", b, "x", b], z) for b in RIGHT]
        level = nxt
    return out


def test(mats, v, depth, seed, extra=True):
    n = v.shape[0]
    rng = random.Random(seed)
    cu = np.array([[rng.randint(0, 1) for _ in range(n)] for _ in range(n)], np.uint8)
    vals = build(mats, v, cu)
    rels = TRAP_RELS + INVOL_RELS + (EXTRA_RELS if extra else [])
    d = rel_diffs(vals, rels, n)
    if d is None:
        return None, 0
    if depth >= 0:
        d += orbit_rel_diffs(vals, n, depth)
    K = closure(mats, d, n)
    return bool(K.red(toint(vals["h"][1]))), len(K.piv)


def polys(degmax):
    return [p for d in range(1, degmax + 1) for p in range(1 << d, 1 << (d + 1)) if p & 1]


def main():
    mode = sys.argv[1]
    if mode == "single":
        degmax, depth, seeds = map(int, sys.argv[2:5])
        for p in polys(degmax):
            for a in units(p):
                if a == 1:
                    continue
                mats, v = ring_module(p, a)
                res = [test(mats, v, depth, s) for s in range(seeds)]
                hits = [s for s, (ok, _) in enumerate(res) if ok]
                print("p=%s a=%s depth %d: Kdim %s hits %s" % (bin(p), bin(a), depth,
                      sorted(set(k for _, k in res)), hits), flush=True)
    elif mode == "pair":
        degmax, depth, seeds = map(int, sys.argv[2:5])
        ps = polys(degmax)
        for p, q in itertools.combinations_with_replacement(ps, 2):
            mats, v = direct_sum([ring_module(p, 0b10), ring_module(q, 0b10)])
            res = [test(mats, v, depth, s) for s in range(seeds)]
            hits = [s for s, (ok, _) in enumerate(res) if ok]
            print("p=%s q=%s depth %d: hits %s" % (bin(p), bin(q), depth, hits), flush=True)
    elif mode == "one":
        p, a, depth, seeds = int(sys.argv[2], 0), int(sys.argv[3], 0), int(sys.argv[4]), int(sys.argv[5])
        mats, v = ring_module(p, a)
        for s in range(seeds):
            print("seed", s, test(mats, v, depth, s), flush=True)


if __name__ == "__main__":
    main()
