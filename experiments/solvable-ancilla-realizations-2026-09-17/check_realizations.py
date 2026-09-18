#!/usr/bin/env python3
"""Exhaustive check: which one-track binary rules tau, stabilized by identity ancilla tracks,
are realized as 2-variable polynomial automata over a small finite group Q?

A realization is a bijection psi: {0,1} x B -> Q (|Q| = 2|B|) and a word with constants
F(q0, q1) (memory {0, m}, site 0 carries the identity ancilla) such that
    psi^-1 F(psi(a0,b0), psi(a1,b1)) = (f(a0,a1), b0)      for all a0,a1,b0,b1.
Equivalently: b(F(q0,q1)) = b(q0), and a(F(q0,q1)) depends only on (a(q0), a(q1)).

Claim `solvable-ancilla-realizations-of-binary-automata-are-affine`: for solvable Q every realized
f is affine over F_2. The script enumerates the whole 2-variable polynomial clone Pol_2(Q) by
breadth-first search over words (generators: x0, x1, their inverses, constants), tests every
function and every psi, and reports the realized rules.

Usage: nice -n 10 timeout 1200 python3 check_realizations.py [--cap N]
"""
import itertools
import sys

import numpy as np


def perm_group(gens, deg):
    e = tuple(range(deg))
    els = [e]
    seen = {e}
    i = 0
    while i < len(els):
        g = els[i]
        i += 1
        for s in gens:
            h = tuple(s[g[x]] for x in range(deg))  # h = s o g
            if h not in seen:
                seen.add(h)
                els.append(h)
    idx = {g: k for k, g in enumerate(els)}
    n = len(els)
    mul = np.zeros((n, n), dtype=np.uint8)
    for a, g in enumerate(els):
        for b, h in enumerate(els):
            mul[a, b] = idx[tuple(g[h[x]] for x in range(deg))]  # g o h
    return mul


def cyc(n, off=0, deg=None):
    deg = deg or n
    p = list(range(deg))
    for i in range(n):
        p[off + i] = off + (i + 1) % n
    return tuple(p)


def quaternion():
    # elements (sign, unit) with units 1,i,j,k; table of unit products
    units = {('1', '1'): (1, '1')}
    base = {('i', 'j'): (1, 'k'), ('j', 'k'): (1, 'i'), ('k', 'i'): (1, 'j'),
            ('j', 'i'): (-1, 'k'), ('k', 'j'): (-1, 'i'), ('i', 'k'): (-1, 'j'),
            ('i', 'i'): (-1, '1'), ('j', 'j'): (-1, '1'), ('k', 'k'): (-1, '1')}
    for u in '1ijk':
        units[('1', u)] = (1, u)
        units[(u, '1')] = (1, u)
    units.update(base)
    els = [(s, u) for s in (1, -1) for u in '1ijk']
    idx = {g: k for k, g in enumerate(els)}
    mul = np.zeros((8, 8), dtype=np.uint8)
    for a, (s1, u1) in enumerate(els):
        for b, (s2, u2) in enumerate(els):
            s, u = units[(u1, u2)]
            mul[a, b] = idx[(s1 * s2 * s, u)]
    return mul


def groups():
    G = {}
    G['Z2'] = (perm_group([cyc(2)], 2), True)
    G['Z4'] = (perm_group([cyc(4)], 4), True)
    G['Z2xZ2'] = (perm_group([cyc(2, 0, 4), cyc(2, 2, 4)], 4), True)
    G['Z6'] = (perm_group([cyc(6)], 6), True)
    G['S3'] = (perm_group([(1, 0, 2), (1, 2, 0)], 3), True)
    G['Z8'] = (perm_group([cyc(8)], 8), True)
    G['Z4xZ2'] = (perm_group([cyc(4, 0, 6), cyc(2, 4, 6)], 6), True)
    G['Z2^3'] = (perm_group([cyc(2, 0, 6), cyc(2, 2, 6), cyc(2, 4, 6)], 6), True)
    G['D4'] = (perm_group([(1, 2, 3, 0), (0, 3, 2, 1)], 4), True)
    G['Q8'] = (quaternion(), True)
    G['A4'] = (perm_group([(1, 2, 0, 3), (1, 0, 3, 2)], 4), True)
    for name, (mul, solv) in G.items():
        n = mul.shape[0]
        i = np.arange(n)
        lhs = mul[mul[i[:, None, None], i[None, :, None]], i[None, None, :]]
        rhs = mul[i[:, None, None], mul[i[None, :, None], i[None, None, :]]]
        assert (lhs == rhs).all(), name
    expected = {'Z2': 2, 'Z4': 4, 'Z2xZ2': 4, 'Z6': 6, 'S3': 6, 'Z8': 8, 'Z4xZ2': 8, 'Z2^3': 8,
                'D4': 8, 'Q8': 8, 'A4': 12}
    for name, k in expected.items():
        assert G[name][0].shape[0] == k, (name, G[name][0].shape)
    return G


def identity_and_inverse(mul):
    n = mul.shape[0]
    e = [a for a in range(n) if all(mul[a, b] == b for b in range(n))][0]
    inv = np.array([[b for b in range(n) if mul[a, b] == e][0] for a in range(n)], dtype=np.uint8)
    return e, inv


def clone2(mul, cap, keep_fn):
    """Breadth-first enumeration of Pol_2(Q), the functions Q^2 -> Q given by words with constants.

    Rows have length n^2. Only 64-bit hashes of visited rows are stored (random linear hash; a collision
    would only drop a function, with probability about total^2 / 2^64). Each new level is passed through
    keep_fn, and only the kept rows are returned. Returns (kept rows, total visited, capped)."""
    n = mul.shape[0]
    e, inv = identity_and_inverse(mul)
    q0 = np.repeat(np.arange(n, dtype=np.uint8), n)
    q1 = np.tile(np.arange(n, dtype=np.uint8), n)
    gens = [q0, q1, inv[q0], inv[q1]] + [np.full(n * n, c, dtype=np.uint8) for c in range(n)]
    gens = np.stack(gens)
    rng = np.random.default_rng(12345)
    R = rng.integers(1, 2**63 - 1, size=n * n, dtype=np.uint64) | np.uint64(1)

    def h(rows):
        out = np.zeros(len(rows), dtype=np.uint64)
        for col in range(n * n):
            out += rows[:, col].astype(np.uint64) * R[col]
        return out

    start = np.full((1, n * n), e, dtype=np.uint8)
    seen = np.sort(h(start))
    kept = [start[keep_fn(start)]]
    frontier_chunks = [start]
    total = 1
    capped = False
    CH = 20000
    while frontier_chunks and not capped:
        # generate the next level in chunks, drop rows seen at earlier levels
        hs, rows_ = [], []
        for chunk in frontier_chunks:
            for c0 in range(0, len(chunk), CH):
                cand = mul[chunk[c0:c0 + CH, None, :], gens[None, :, :]].reshape(-1, n * n)
                hc_u, first = np.unique(h(cand), return_index=True)
                new = ~np.isin(hc_u, seen, assume_unique=True)
                hs.append(hc_u[new])
                rows_.append(cand[first[new]])
        if not hs:
            break
        # deduplicate within the level: sort all hashes once, keep the first row of each run
        hc = np.concatenate(hs)
        order = np.argsort(hc, kind='stable')
        hc_sorted = hc[order]
        firsts = np.ones(len(hc_sorted), dtype=bool)
        firsts[1:] = hc_sorted[1:] != hc_sorted[:-1]
        sel = order[firsts]
        del hs
        offsets = np.cumsum([0] + [len(r) for r in rows_])
        next_chunks = []
        for k, r in enumerate(rows_):
            loc = sel[(sel >= offsets[k]) & (sel < offsets[k + 1])] - offsets[k]
            if len(loc):
                rows = r[np.sort(loc)]
                next_chunks.append(rows)
                kept.append(rows[keep_fn(rows)])
        del rows_
        seen = np.union1d(seen, hc_sorted[firsts])
        total += int(firsts.sum())
        frontier_chunks = next_chunks
        if total > cap:
            capped = True
    return np.concatenate(kept), total, capped


def is_affine(tt):
    # tt = (f(0,0), f(0,1), f(1,0), f(1,1)); affine iff f00+f01+f10+f11 = 0 mod 2
    return (sum(tt) % 2) == 0


def realizations(F, n):
    """Yield (pairing, labeling, truth table) for one function table F of shape (n, n)."""
    forced = {}
    for q0 in range(n):
        others = set(int(v) for v in F[q0]) - {q0}
        if len(others) > 1:
            return
        if others:
            p = others.pop()
            if forced.get(q0, p) != p or forced.get(p, q0) != q0:
                return
            forced[q0] = p
            forced[p] = q0
    free = [q for q in range(n) if q not in forced]

    def matchings(items):
        if not items:
            yield []
            return
        a = items[0]
        for i in range(1, len(items)):
            rest = items[1:i] + items[i + 1:]
            for m in matchings(rest):
                yield [(a, items[i])] + m

    base = []
    done = set()
    for q, p in forced.items():
        if q not in done:
            base.append((q, p))
            done.update((q, p))
    for m in matchings(free):
        pairs = base + m
        for bits in itertools.product((0, 1), repeat=len(pairs)):  # all labelings, no flip normalization
            a = np.zeros(n, dtype=np.uint8)
            for (q, p), bit in zip(pairs, bits):
                a[q], a[p] = bit, 1 - bit
            out = a[F]  # a-value of F(q0, q1)
            tt = {}
            ok = True
            A0 = a[:, None].repeat(n, 1)
            A1 = a[None, :].repeat(n, 0)
            for s in (0, 1):
                for t in (0, 1):
                    vals = out[(A0 == s) & (A1 == t)]
                    if (vals != vals[0]).any():
                        ok = False
                        break
                    tt[(s, t)] = int(vals[0])
                if not ok:
                    break
            if ok:
                yield pairs, a.copy(), (tt[(0, 0)], tt[(0, 1)], tt[(1, 0)], tt[(1, 1)])


def prefilter_mask(rows, n):
    """F(q0, .) takes at most one value other than q0, so the ancilla of q0 can be preserved."""
    T = rows.reshape(-1, n, n)
    q = np.arange(n, dtype=np.uint8)[None, :, None]
    ne = T != q
    mn = np.where(ne, T, 255).min(axis=2)
    mx = np.where(ne, T, 0).max(axis=2)
    return ((mn == 255) | (mn == mx)).all(axis=1)


def pipeline_control(mul):
    """A non-affine rule f = a0 AND a1, pushed through a psi, must be detected as realized."""
    n = mul.shape[0]
    pairs = [(2 * i, 2 * i + 1) for i in range(n // 2)]
    a = np.array([i % 2 for i in range(n)])
    b = np.array([i // 2 for i in range(n)])
    psi = {(int(a[q]), int(b[q])): q for q in range(n)}
    F = np.zeros((n, n), dtype=np.uint8)
    for q0 in range(n):
        for q1 in range(n):
            F[q0, q1] = psi[(int(a[q0] & a[q1]), int(b[q0]))]
    return any(tt == (0, 0, 0, 1) for _, _, tt in realizations(F, n))


def main():
    cap = 5_000_000
    if '--cap' in sys.argv:
        cap = int(sys.argv[sys.argv.index('--cap') + 1])
    G = groups()
    order = ['Z2', 'Z4', 'Z2xZ2', 'Z6', 'S3', 'Z8', 'Z4xZ2', 'Z2^3', 'D4', 'Q8', 'A4']
    if '--only' in sys.argv:
        order = sys.argv[sys.argv.index('--only') + 1].split(',')
    grand_nonaffine = 0
    for name in order:
        mul, _ = G[name]
        n = mul.shape[0]
        rows, total, capped = clone2(mul, cap, lambda r: prefilter_mask(r, n))
        rules = {}
        count = 0
        for i in range(len(rows)):
            F = rows[i].reshape(n, n)
            for pairs, a, tt in realizations(F, n):
                count += 1
                rules[tt] = rules.get(tt, 0) + 1
        nonaffine = {tt: c for tt, c in rules.items() if not is_affine(tt)}
        grand_nonaffine += len(nonaffine)
        depends_on_a1 = sorted(tt for tt in rules if tt[0] != tt[1] or tt[2] != tt[3])
        print(f"{name}: |Q|={n} |Pol_2(Q)|={total}{' (CAPPED, incomplete)' if capped else ' (complete)'}"
              f" prefilter={len(rows)} realizations={count}")
        print(f"   realized truth tables f(00,01,10,11): {sorted(rules)}")
        print(f"   realized rules reading a1 (non-sitewise): {depends_on_a1}")
        print(f"   non-affine realized: {nonaffine if nonaffine else 'none'}")
        print(f"   pipeline control (AND pushed through psi detected): {pipeline_control(mul)}")
        sys.stdout.flush()
    print(f"TOTAL non-affine realized rules over all groups: {grand_nonaffine}")


if __name__ == '__main__':
    main()
