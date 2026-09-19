#!/usr/bin/env python3
"""Independent check of a head-keeping finite quotient of Gamma_trap.

Model: W = M_2(A), A = F_2[x]/(x^4 + 1), left EL_2 by Y -> aY (as = x12(x),
at = x12(x^{-1}), c = x21(1)), right by Y -> Y b (b1 = x12(1), bs = x21(x),
bt = x21(x^{-1})), N_W = W x (W (x) W) with cocycle w (x) w', G0 acting by
(Aw, A z A^T), u = (E_11, c_u) with c_u random (seeded, saved to hit_cu.txt).

This file does NOT import tensor_model.  It builds the group
G = (N_W / K) x| G0 with K the G0-closure of the relator differences, then
checks from scratch, by explicit multiplication in G:
  * K is G0-stable (so G is a group; C is central in N_W);
  * every relator of Gamma_trap (R1-R3, LR, UU, involutions) is 1 in G;
  * h = u * ust is not 1 in G;
  * which EXTRA_RELS hold, and whether the head survives them too;
  * whether (C1) holds at z = u (it does; the orbit trap forces a failure
    elsewhere on Z, found by `orbit`).
Usage: python3 verify_hit.py [seed]          full check, writes hit_cu_seed<seed>.txt
       python3 verify_hit.py LO HI           head survival for seeds LO..HI-1
       python3 verify_hit.py orbit SEED      right d-orbit Z and (C1)/(C2) failures
       python3 verify_hit.py depth LO HI k   add EXTRA_RELS and (C1),(C2) at right
                                             words of depth <= k (all true in P)
Env VERIFY_P overrides the modulus (default 0b10001 = x^4 + 1).
"""

import random
import sys

import numpy as np

from tensor_search import ring_module
from words import DERIVED, TRAP_RELS, INVOL_RELS, EXTRA_RELS, LEFT, RIGHT

import os

P = int(os.environ.get("VERIFY_P", "0b10001"), 0)  # default x^4 + 1
NDIM = 4 * (P.bit_length() - 1)


def mm(A, B):
    return (A.astype(np.int64) @ B.astype(np.int64) % 2).astype(np.uint8)


class Basis:
    """Row-echelon basis of a subspace of F_2^N, vectors as python ints."""

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

    def dim(self):
        return len(self.piv)


def toint(z):
    out = 0
    for b in np.flatnonzero(z.reshape(-1)):
        out |= 1 << int(b)
    return out


def mul(X, Y):
    (w, z, A), (w2, z2, B) = X, Y
    w2a = mm(A, w2.reshape(-1, 1)).reshape(-1)
    z2a = mm(mm(A, z2), A.T)
    return (w ^ w2a, z ^ z2a ^ np.outer(w, w2a).astype(np.uint8), mm(A, B))


def word(vals, wd, n):
    acc = (np.zeros(n, np.uint8), np.zeros((n, n), np.uint8), np.eye(n, dtype=np.uint8))
    for g in wd:
        acc = mul(acc, vals[g])
    return acc


def build(cu):
    mats, v = ring_module(P)
    n = v.shape[0]
    zw, zz = np.zeros(n, np.uint8), np.zeros((n, n), np.uint8)
    vals = {g: (zw, zz, mats[g]) for g in LEFT + RIGHT}
    vals["u"] = (v.copy(), cu, np.eye(n, dtype=np.uint8))
    for name, wd in DERIVED:
        vals[name] = word(vals, wd, n)
    return mats, vals, n


def diffs(vals, rels, n):
    """For each relator lhs = rhs: None if the W- or G0-parts differ,
    else z_lhs + z_rhs (then lhs = rhs in G iff this lies in K)."""
    out = {}
    for name, l, r in rels:
        X, Y = word(vals, l, n), word(vals, r, n)
        if (X[0] != Y[0]).any() or (X[2] != Y[2]).any():
            out[name] = None
        else:
            out[name] = toint(X[1] ^ Y[1])
    return out


def closure(mats, gens, n):
    K = Basis()
    queue = [g for g in gens if g]
    while queue:
        x = K.add(queue.pop())
        if not x:
            continue
        z = np.zeros(n * n, np.uint8)
        for b in range(n * n):
            z[b] = x >> b & 1
        z = z.reshape(n, n)
        for A in mats.values():
            y = toint(mm(mm(A, z), A.T))
            if K.red(y):
                queue.append(y)
    return K


def is_stable(K, mats, n):
    for x in list(K.piv.values()):
        z = np.array([x >> b & 1 for b in range(n * n)], np.uint8).reshape(n, n)
        for A in mats.values():
            if K.red(toint(mm(mm(A, z), A.T))):
                return False
    return True


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    rng = random.Random(seed)
    n = NDIM
    cu = np.array([[rng.randint(0, 1) for _ in range(n)] for _ in range(n)], np.uint8)
    mats, vals, n = build(cu)
    for g, A in mats.items():
        assert not (mm(A, A) ^ np.eye(n, dtype=np.uint8)).any(), g
    base = diffs(vals, TRAP_RELS + INVOL_RELS, n)
    bad = [k for k, d in base.items() if d is None]
    print("relators failing at W/G0 level:", bad)
    K = closure(mats, list(base.values()), n)
    print("K dim %d of %d, G0-stable: %s" % (K.dim(), n * n, is_stable(K, mats, n)))
    fails = [k for k, d in base.items() if d is not None and K.red(d)]
    print("relators not in K:", fails)
    hw, hz, hA = vals["h"]
    central = not hw.any() and not (hA ^ np.eye(n, dtype=np.uint8)).any()
    surv = bool(K.red(toint(hz)))
    print("head: w-part 0 and G0-part 1: %s; head != 1 in G: %s" % (central, surv))
    ex = diffs(vals, EXTRA_RELS, n)
    held = [k for k, d in ex.items() if d is not None and not K.red(d)]
    wfail = [k for k, d in ex.items() if d is None]
    print("EXTRA_RELS holding in G (%d/%d):" % (len(held), len(ex)), held)
    print("EXTRA_RELS failing at W/G0 level:", wfail)
    okex = [d for d in ex.values() if d is not None]
    K2 = closure(mats, list(base.values()) + okex, n)
    print("adding every EXTRA_REL that holds at W/G0 level: K dim %d, head survives %s"
          % (K2.dim(), bool(K2.red(toint(hz)))))
    for b in RIGHT:
        wd1, wd2 = [b, "u", b], ["c", "u", "c"]
        d = diffs(vals, [("C1_" + b, wd1 + wd2, wd2 + wd1)], n)["C1_" + b]
        print("(C1) at z=u, b=%s: [bub, cuc] = 1 in G: %s"
              % (b, d is not None and not K.red(d)))
    with open("hit_cu_seed%d.txt" % seed, "w") as f:
        for row in cu:
            f.write("".join(str(int(x)) for x in row) + "\n")
    return surv


def full_red(K, v):
    """Canonical representative of v mod K (clear every pivot bit)."""
    for p in sorted(K.piv, reverse=True):
        if v >> p & 1:
            v ^= K.piv[p]
    return v


def orbit_check(seed, cap=20000):
    """Enumerate the right d-orbit Z of u in G and test the orbit-trap
    hypotheses (C1) [bzb, czc] = 1 on Z and (C2) [bz'b, az'a] = 1 on d_c(Z)."""
    rng = random.Random(seed)
    n = NDIM
    cu = np.array([[rng.randint(0, 1) for _ in range(n)] for _ in range(n)], np.uint8)
    mats, vals, n = build(cu)
    base = diffs(vals, TRAP_RELS + INVOL_RELS, n)
    K = closure(mats, list(base.values()), n)
    I = np.eye(n, dtype=np.uint8)

    def key(X):
        return (toint(X[0]), full_red(K, toint(X[1])))

    def d(g, X):
        return word({"x": X, "g": vals[g]}, ["x", "g", "x", "g"], n)

    def commute(X, Y):
        XY, YX = mul(X, Y), mul(Y, X)
        return not (XY[0] ^ YX[0]).any() and not K.red(toint(XY[1] ^ YX[1]))

    def conj(g, X):
        return word({"x": X, "g": vals[g]}, ["g", "x", "g"], n)

    seen = {key(vals["u"]): vals["u"]}
    queue = [vals["u"]]
    while queue and len(seen) < cap:
        X = queue.pop()
        for b in RIGHT:
            Y = d(b, X)
            k = key(Y)
            if k not in seen:
                seen[k] = Y
                queue.append(Y)
    Z = list(seen.values())
    print("|Z| = %d (complete: %s)" % (len(Z), not queue))
    c1 = [(b, i) for i, z in enumerate(Z) for b in RIGHT
          if not commute(conj(b, z), conj("c", z))]
    c2 = [(b, a, i) for i, z in enumerate(Z) for b in RIGHT for a in ["as", "at"]
          if not commute(conj(b, d("c", z)), conj(a, d("c", z)))]
    print("(C1) failures on Z: %d; (C2) failures on d_c(Z): %d" % (len(c1), len(c2)))
    print("first failures:", c1[:4], c2[:4])
    del I


def orbit_rel_diffs(vals, n, depth):
    """C-parts of the P-true relators (C1) [bzb, czc] = 1 and (C2)
    [bz'b, az'a] = 1, z' = d_c z, for z = d_(b_1)...d_(b_j) u with j <= depth
    (right words; all these relators hold in P since <<u>> is abelian there)."""
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
                assert not (XY[0] ^ YX[0]).any()
                out.append(toint(XY[1] ^ YX[1]))
            nxt += [w(["x", b, "x", b], z) for b in RIGHT]
        level = nxt
    return out


def scan_depth(lo, hi, depth):
    n = NDIM
    hits = []
    for seed in range(lo, hi):
        rng = random.Random(seed)
        cu = np.array([[rng.randint(0, 1) for _ in range(n)] for _ in range(n)], np.uint8)
        mats, vals, n = build(cu)
        gens = list(diffs(vals, TRAP_RELS + INVOL_RELS + EXTRA_RELS, n).values())
        K = closure(mats, gens + orbit_rel_diffs(vals, n, depth), n)
        s = bool(K.red(toint(vals["h"][1])))
        print("seed %d depth %d: Kdim %d survives %s" % (seed, depth, K.dim(), s))
        if s:
            hits.append(seed)
    print("hits:", hits)


def scan(lo, hi):
    """Head survival for c_u from seeds lo..hi-1 (quick, no extra checks)."""
    n = NDIM
    hits = []
    for seed in range(lo, hi):
        rng = random.Random(seed)
        cu = np.array([[rng.randint(0, 1) for _ in range(n)] for _ in range(n)], np.uint8)
        mats, vals, n = build(cu)
        base = diffs(vals, TRAP_RELS + INVOL_RELS, n)
        K = closure(mats, list(base.values()), n)
        s = bool(K.red(toint(vals["h"][1])))
        print("seed %d: Kdim %d survives %s" % (seed, K.dim(), s))
        if s:
            hits.append(seed)
    print("hits:", hits)


if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[1] == "orbit":
        orbit_check(int(sys.argv[2]))
    elif len(sys.argv) > 4 and sys.argv[1] == "depth":
        scan_depth(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    elif len(sys.argv) > 2:
        scan(int(sys.argv[1]), int(sys.argv[2]))
    else:
        sys.exit(0 if main() else 1)
