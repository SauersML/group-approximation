#!/usr/bin/env python3
"""Exhaustive F_p search for two-copy port solutions in a Steenbock-type model.

Model.  Gamma has n lines; line i has row r = i + 1 and positions
    0, I1 = M, I2 = 2M, O1 = 3M, O2 = 4M, C = 5M,   M = 6^(r-1)  (separated rows)
or M = 1 for every line (degenerate control).  Four fixed-point-free permutations s1..s4 give the b-edges
    x1: (l, 0)  -> (s1[l], I1)      x2: (l, C)  -> (s2[l], I2)
    x3: (l, O1) -> (s3[l], C)       x4: (l, O2) -> (s4[l], 0)
exactly as in Steenbock's gluing table.  Two copies of the same Gamma are glued by
  * merges   ((i1, i2, s)): line i1 of copy 0 and line i2 of copy 1 are one <a>-coset; copy-1 position x
               sits at coset coordinate x + s;
  * bridges  (((m, i, p), (m', i', p'))): an extra b-edge between the two copies.
A vertex is (coset, coordinate).  The union of both copies' b-edges (shared edges counted once) and the
bridges is the b-edge set E.  A model is rejected if some vertex gets two different outgoing (or incoming)
b-edges, since z b is unique in the group.

Port system.  Exact encoding (Lemma 2 of the one-copy proof, and its two-copy version) says that a relation
alpha (u + w b) = 0 supported on the union is the same as a vector c in k^E with
    P_T = - sum_{e into T} c_e t^{head(e)},   Q_T = sum_{e out of T} c_e t^{tail(e)},
such that all pairs (P_T, Q_T) are proportional, i.e. P_T Q_T' = P_T' Q_T for all cosets T, T'
(then (u, w) = (P_T0, Q_T0)/gcd and f_T = P_T / u).  A nonzero solution is a model zero divisor.

Search (exhaustive over F_p).  Order the cosets.  A nonzero solution has a first active coset T0; all
earlier cosets are inactive, so their incident c_e vanish, and Q_T0 != 0.  For each T0 and each assignment
of the remaining T0-incident edges with Q_T0 != 0, normalized so that the first nonzero Q_T0 value is 1,
the conditions P_T Q_T0 = P_T0 Q_T (T != T0) are linear in c.  The model has a solution iff one of these
affine systems is consistent.

The model graph Phi has short cycles, so the model does NOT see the length lemma of the two-copy proof
(a port cycle through <= 5 cosets is a relation of length <= 10 < 5 gamma/8 - 1 in the real core).  It tests
the algebraic part: which gluings admit coefficient solutions at all, and how many clean active lines a
solution uses in each copy.
"""
import random
import sys
import time
from collections import deque

import numpy as np

KINDS = ("Z", "I1", "I2", "O1", "O2", "C")


def positions(i, sep):
    m = 6 ** i if sep else 1
    return dict(Z=0, I1=m, I2=2 * m, O1=3 * m, O2=4 * m, C=5 * m)


def derangement(n, rng):
    while True:
        p = list(range(n))
        rng.shuffle(p)
        if all(p[i] != i for i in range(n)):
            return p


def make_gamma(n, seed):
    rng = random.Random(seed)
    return [derangement(n, rng) for _ in range(4)]


def gamma_edges(n, perms, sep):
    """b-edges of Gamma as ((line, pos), (line, pos), label)."""
    out = []
    for l in range(n):
        pl = positions(l, sep)
        for j, (src, dst) in enumerate((("Z", "I1"), ("C", "I2"), ("O1", "C"), ("O2", "Z"))):
            i = perms[j][l]
            out.append(((l, pl[src]), (i, positions(i, sep)[dst]), j + 1))
    return out


class Model:
    def __init__(self, name, n, perms, sep=True, merges=(), bridges=(), copies=2):
        self.name, self.n, self.sep = name, n, sep
        self.cid, self.off = {}, {}
        cosets = []
        for m in range(copies):
            for i in range(n):
                self.cid[(m, i)] = len(cosets)
                self.off[(m, i)] = 0
                cosets.append([(m, i)])
        for (i1, i2, s) in merges:
            c1, c2 = self.cid[(0, i1)], self.cid[(1, i2)]
            cosets[c1].append((1, i2))
            cosets[c2] = None
            self.cid[(1, i2)] = c1
            self.off[(1, i2)] = s
        keep = [k for k, c in enumerate(cosets) if c is not None]
        ren = {k: t for t, k in enumerate(keep)}
        self.cosets = [cosets[k] for k in keep]
        for key in self.cid:
            self.cid[key] = ren[self.cid[key]]
        self.bridge_cosets = set()
        edges = set()
        for m in range(copies):
            for (a, b, _) in gamma_edges(n, perms, sep):
                edges.add((self.vert(m, *a), self.vert(m, *b)))
        for (x, y) in bridges:
            vx, vy = self.vert(*x), self.vert(*y)
            edges.add((vx, vy))
            self.bridge_cosets |= {vx[0], vy[0]}
        self.edges = sorted(edges)
        self.valid = True
        tails, heads = {}, {}
        for e, (t, h) in enumerate(self.edges):
            if t in tails or h in heads or t[0] == h[0]:
                self.valid = False
            tails[t], heads[h] = e, e
        self.nc = len(self.cosets)
        self.ins = [[] for _ in range(self.nc)]
        self.outs = [[] for _ in range(self.nc)]
        for e, (t, h) in enumerate(self.edges):
            self.outs[t[0]].append((e, t[1]))
            self.ins[h[0]].append((e, h[1]))

    def vert(self, m, i, p):
        return (self.cid[(m, i)], p + self.off[(m, i)])

    def clean(self, T):
        return len(self.cosets[T]) == 1 and T not in self.bridge_cosets

    def copy_of(self, T):
        return {m for (m, _) in self.cosets[T]}


def solve_mod(A, b, p):
    """Return (consistent, rank, particular solution) of A x = b over F_p."""
    M = np.concatenate([A % p, (b % p)[:, None]], axis=1).astype(np.int64)
    rows, cols = A.shape
    piv, r = [], 0
    for c in range(cols):
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0:
            continue
        k = r + nz[0]
        if k != r:
            M[[r, k]] = M[[k, r]]
        M[r] = (M[r] * pow(int(M[r, c]), p - 2, p)) % p
        col = M[:, c].copy()
        col[r] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr):
            M[nzr] = (M[nzr] - np.outer(col[nzr], M[r])) % p
        piv.append(c)
        r += 1
        if r == rows:
            break
    if r < rows and np.any(M[r:, cols] % p):
        return False, r, None
    x = np.zeros(cols, dtype=np.int64)
    for k, c in enumerate(piv):
        x[c] = M[k, cols]
    return True, r, x


def search(model, p, max_free=12, want=3):
    """Exhaustive search; returns (number of consistent (T0, a), samples, skipped T0 list)."""
    E = len(model.edges)
    order = sorted(range(model.nc), key=lambda T: len(model.ins[T]) + len(model.outs[T]))
    dead = set()          # edges forced to 0 (incident to earlier cosets)
    found, samples, skipped = 0, [], []
    for T0 in order:
        inc = sorted({e for (e, _) in model.ins[T0] + model.outs[T0]})
        free = [e for e in inc if e not in dead]
        outs0 = [(e, x) for (e, x) in model.outs[T0] if e not in dead]
        ins0 = [(e, x) for (e, x) in model.ins[T0] if e not in dead]
        if not outs0:
            dead |= set(inc)
            continue
        if len(free) > max_free:
            skipped.append((T0, len(free)))
            dead |= set(inc)
            continue
        # rows: (T, monomial) for T != T0; A_f[row, e] coefficients, linear in a_f.
        rowid, Af = {}, {f: {} for f in free}
        for T in range(model.nc):
            if T == T0:
                continue
            for (e, x) in model.ins[T]:
                if e in dead:
                    continue
                for (f, x0) in outs0:
                    r = rowid.setdefault((T, x + x0), len(rowid))
                    Af[f][(r, e)] = Af[f].get((r, e), 0) - 1
            for (e, y) in model.outs[T]:
                if e in dead:
                    continue
                for (f, y0) in ins0:
                    r = rowid.setdefault((T, y + y0), len(rowid))
                    Af[f][(r, e)] = Af[f].get((r, e), 0) + 1
        R = len(rowid)
        dense = {}
        for f in free:
            D = np.zeros((R, E), dtype=np.int64)
            for (r, e), v in Af[f].items():
                D[r, e] += v
            dense[f] = D
        fixed_rows = np.zeros((E, E), dtype=np.int64)
        fixed_rows[np.arange(E), np.arange(E)] = 1
        fix_mask = np.array([(e in dead) or (e in free) for e in range(E)])
        Fix = fixed_rows[fix_mask]
        fix_idx = np.nonzero(fix_mask)[0]
        out_free = [e for (e, _) in outs0]
        for code in range(p ** len(free)):
            a, cc = {}, code
            for f in free:
                a[f] = cc % p
                cc //= p
            qv = [a[e] for e in out_free]
            nzq = [v for v in qv if v]
            if not nzq or nzq[0] != 1:
                continue
            A = sum((a[f] * dense[f] for f in free if a[f]), np.zeros((R, E), dtype=np.int64))
            bfix = np.array([a.get(e, 0) if e in free else 0 for e in fix_idx], dtype=np.int64)
            AA = np.concatenate([A, Fix], axis=0)
            bb = np.concatenate([np.zeros(R, dtype=np.int64), bfix])
            ok, rank, x = solve_mod(AA, bb, p)
            if ok:
                found += 1
                if len(samples) < want:
                    samples.append((T0, x, E - rank))
        dead |= set(inc)
    return found, samples, skipped


def describe(model, x, p):
    act = [T for T in range(model.nc)
           if any(x[e] % p for (e, _) in model.ins[T] + model.outs[T])]
    clean_per_copy = {m: sum(1 for T in act if model.clean(T) and model.copy_of(T) == {m}) for m in (0, 1)}
    adj = {T: set() for T in act}
    for e, (t, h) in enumerate(model.edges):
        if x[e] % p:
            adj[t[0]].add(h[0])
    best = None
    for s in act:
        dist, dq = {s: 0}, deque([s])
        while dq:
            v = dq.popleft()
            for w in adj[v]:
                if w == s:
                    L = dist[v] + 1
                    best = L if best is None else min(best, L)
                elif w not in dist:
                    dist[w] = dist[v] + 1
                    dq.append(w)
    names = [("+".join(f"{m}:{i}" for (m, i) in model.cosets[T])) for T in act]
    return dict(active=len(act), clean=clean_per_copy, cycle=best, cosets=names)


def build_models(n, perms, sep=True, tag=""):
    P = lambda i: positions(i, sep)
    inv4 = [0] * n
    for l in range(n):
        inv4[perms[3][l]] = l
    ms = []
    ms.append(("disjoint", "allowed", Model("disjoint" + tag, n, perms, sep)))
    # single bridge: hanging vertex of copy 0 -> non-target vertex of copy 1
    for (i, j, pk, qk) in ((0, 1, "I1", "O1"), (2, 4, "I2", "O2"), (5, 0, "I1", "O2"), (3, 3, "I2", "O1")):
        ms.append((f"bridge 0:{i}.{pk}->1:{j}.{qk}", "allowed",
                   Model("bridge" + tag, n, perms, sep, bridges=[((0, i, P(i)[pk]), (1, j, P(j)[qk]))])))
    ms.append(("bridge generic 0:1.(I1+1)->1:2.(O1+1)", "allowed",
               Model("bridge" + tag, n, perms, sep, bridges=[((0, 1, P(1)["I1"] + 1), (1, 2, P(2)["O1"] + 1))])))
    # two bridges (excluded by the bridge corollary)
    for (i, j, i2, j2) in ((0, 1, 1, 0), (2, 4, 4, 3), (1, 1, 5, 2)):
        ms.append((f"two bridges 0:{i}->1:{j}, 1:{i2}->0:{j2}", "excluded",
                   Model("2bridge" + tag, n, perms, sep, bridges=[((0, i, P(i)["I1"]), (1, j, P(j)["O1"])),
                                                                ((1, i2, P(i2)["I2"]), (0, j2, P(j2)["O2"]))])))
    # one shared coset, no shared vertex / one shared hanging vertex
    for (i1, i2) in ((0, 1), (2, 5), (3, 3)):
        ms.append((f"shared coset 0:{i1}~1:{i2} shift 1", "allowed",
                   Model("shared1" + tag, n, perms, sep, merges=[(i1, i2, 1)])))
        s = P(i1)["I1"] - P(i2)["I2"]
        ms.append((f"shared coset 0:{i1}~1:{i2} sharing a hanging vertex", "allowed",
                   Model("shared1v" + tag, n, perms, sep, merges=[(i1, i2, s)])))
    # shared b-edge: Gamma-edge e in copy 0 equals Gamma-edge e' != e in copy 1
    ge = gamma_edges(n, perms, sep)
    rng = random.Random(7)
    cnt = 0
    for _ in range(400):
        e, f = rng.sample(range(len(ge)), 2)
        (l, p0), (i, q0), _ = ge[e]
        (l2, p1), (i2, q1), _ = ge[f]
        if l == l2 and i == i2:
            continue
        m = Model("sharededge" + tag, n, perms, sep, merges=[(l, l2, p0 - p1), (i, i2, q0 - q1)])
        if m.valid:
            ms.append((f"shared b-edge {ge[e][:2]} = {ge[f][:2]}", "allowed", m))
            cnt += 1
        if cnt == 4:
            break
    # shared 2-run through position 0: (l, O2) -> (i, 0) -> (k, I1)
    cnt = 0
    for i in range(n):
        for i2 in range(n):
            if i2 == i:
                continue
            l, k, l2, k2 = inv4[i], perms[0][i], inv4[i2], perms[0][i2]
            if len({l, i, k}) < 3 or len({l2, i2, k2}) < 3:
                continue
            m = Model("sharedrun" + tag, n, perms, sep,
                      merges=[(l, l2, P(l)["O2"] - P(l2)["O2"]), (i, i2, 0), (k, k2, P(k)["I1"] - P(k2)["I1"])])
            if m.valid and cnt < 4:
                ms.append((f"shared 2-run through 0:{i}.0 = 1:{i2}.0", "allowed", m))
                cnt += 1
    # two shared cosets with no shared run (excluded by the shared-coset corollary)
    for (a1, a2, b1, b2) in ((0, 1, 2, 3), (1, 4, 3, 0), (4, 4, 5, 5)):
        ms.append((f"two shared cosets 0:{a1}~1:{a2}, 0:{b1}~1:{b2}, no shared run", "excluded",
                   Model("shared2" + tag, n, perms, sep, merges=[(a1, a2, 1), (b1, b2, 1)])))
    # shared coset plus a bridge (excluded by the bridge corollary)
    ms.append(("shared coset 0:0~1:1 plus bridge 0:2->1:3", "excluded",
               Model("sharedbridge" + tag, n, perms, sep, merges=[(0, 1, 1)],
                     bridges=[((0, 2, P(2)["I1"]), (1, 3, P(3)["O1"]))])))
    return ms


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    primes = [int(t) for t in sys.argv[3].split(",")] if len(sys.argv) > 3 else [2, 3]
    perms = make_gamma(n, seed)
    print(f"n = {n} lines per copy, seed {seed}, permutations x1..x4 = {perms}")
    t0 = time.time()
    for sep, tag in ((True, ""), (False, "-degenerate")):
        print(f"\n=== {'separated rows (M = 6^(r-1))' if sep else 'DEGENERATE control: all lines positions 0..5'} ===")
        models = build_models(n, perms, sep, tag)
        if not sep:
            models = [mm for mm in models if mm[0] == "disjoint" or mm[0].startswith("bridge 0:0")
                      or mm[0].startswith("shared coset 0:0~1:1 shift")]
        seen = set()
        for (label, status, m) in models:
            if not m.valid:
                print(f"[{status}] {label}: gluing inconsistent (two b-edges at one vertex); skipped")
                continue
            # F_2 on every model; the slower F_3 run on the first valid model of each gluing type
            first = m.name not in seen
            seen.add(m.name)
            for p in primes:
                if p != 2 and not first:
                    continue
                mf = 12 if p == 2 else 9
                found, samples, skipped = search(m, p, max_free=mf)
                line = f"[{status}] {label}: F_{p}: cosets {m.nc}, edges {len(m.edges)}, consistent (T0, a) = {found}"
                if skipped:
                    line += f", NOT exhaustive (skipped T0 with free degree > {mf}: {skipped})"
                print(line)
                for (T0, x, nul) in samples[:2]:
                    d = describe(m, x, p)
                    print(f"      sample from T0 = {T0}: solution-space dim {nul}, active {d['active']} {d['cosets']},"
                          f" clean active per copy {d['clean']}, shortest port cycle {d['cycle']}")
                sys.stdout.flush()
    print(f"\ntotal time {time.time() - t0:.1f} s")


if __name__ == "__main__":
    main()
