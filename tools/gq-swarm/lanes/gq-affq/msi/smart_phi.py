#!/usr/bin/env python3
"""Learn a deletion rule phi (window of radius r -> delete one cell near the head, shift head,
set phase-2 shape) with phi(S^3 y) = S(phi(y)) on A = {phase 0}, by constraint pruning;
then validate on fresh long orbits and test that phi: A -> Y is a bijection."""
import random, sys, collections
from smart_core import Conf, step, inY, S, letters, offsets, window, rand_conf, same

D = 2       # deletion offsets and head shifts in [-D, D]
W = 120     # materialised window for edits
R_EQ = int(__import__("os").environ.get("REQ","40"))  # config equality radius


def apply_edit(c, e):
    j, hs, sh = e
    cells = [c.cell(c.h + i) for i in range(-W, W + 1)]
    hi = W
    del cells[hi + j]
    if j < 0:
        hi -= 1
    t = {i - hi - hs: v for i, v in enumerate(cells)}
    return Conf(t, 0, sh, 2, c.rng)


EDITS = [(j, hs, sh) for j in range(-D, D + 1) for hs in range(-D, D + 1) for sh in 'bdpq']


def phase_table(rng, n):
    tab = collections.defaultdict(set)
    for _ in range(n):
        c = rand_conf(rng, rng.randrange(100, 3000))
        L = letters(c, 240)
        o = offsets(L)
        if len(o) != 1:
            continue
        cc = c.copy()
        for i in range(90):
            tab[window(cc, 1)].add((i - o[0]) % 3)
            S(cc)
    assert all(len(v) == 1 for v in tab.values()), 'phase not radius-1 readable'
    return {k: next(iter(v)) for k, v in tab.items()}


def samples_A(rng, PH, n, burn=(100, 3000)):
    out = []
    while len(out) < n:
        c = rand_conf(rng, rng.randrange(*burn))
        k = 0
        while PH[window(c, 1)] != 0:
            S(c)
            k += 1
        out.append(c)
    return out


def sig(c):
    return (c.s, c.ph, tuple(c.cell(c.h + i) for i in range(-R_EQ, R_EQ + 1)))


def S3(c):
    c = c.copy()
    for _ in range(3):
        S(c)
    return c


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    r = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    NTR = int(sys.argv[3]) if len(sys.argv) > 3 else 600
    rng = random.Random(seed)
    PH = phase_table(rng, 120)
    print('phase table: windows', len(PH), 'counts', collections.Counter(PH.values()))
    # training pairs along orbits (so that y3 windows are also covered as y windows)
    train = []
    for y in samples_A(rng, PH, NTR // 20):
        cur = y
        for _ in range(20):
            nxt = S3(cur)
            train.append((cur, nxt))
            cur = nxt
    C = collections.defaultdict(lambda: set(EDITS))
    # precompute per pair: images
    pre = []
    for y, y3 in train:
        wy, w3 = window(y, r), window(y3, r)
        Sy = {}
        for e in C[wy]:
            z = apply_edit(y, e)
            if inY(z):
                zz = z.copy(); S(zz)
                Sy[e] = sig(zz)
        im3 = collections.defaultdict(set)
        for e in C[w3]:
            z = apply_edit(y3, e)
            if inY(z):
                im3[sig(z)].add(e)
        pre.append((wy, w3, Sy, im3))
    changed, rounds = True, 0
    while changed:
        changed = False
        rounds += 1
        for wy, w3, Sy, im3 in pre:
            good1, good3 = set(), set()
            for e1, s1 in Sy.items():
                if e1 not in C[wy]:
                    continue
                hit = im3.get(s1, set()) & C[w3]
                if hit:
                    good1.add(e1); good3 |= hit
            if C[wy] - good1:
                C[wy] &= good1; changed = True
            if C[w3] - good3:
                C[w3] &= good3; changed = True
    sizes = collections.Counter(len(v) for v in C.values())
    print(f'radius {r}: windows {len(C)}, rounds {rounds}, candidate-set sizes {dict(sizes)}')
    empty = [w for w, v in C.items() if not v]
    print('empty windows:', len(empty), empty[:5])
    if empty:
        return
    rule = {w: sorted(v)[0] for w, v in C.items()}

    def phi(c):
        w = window(c, r)
        if w not in rule:
            return None
        return apply_edit(c, rule[w])

    # validation on fresh samples and long orbits
    bad = unseen = ok = 0
    for y in samples_A(random.Random(seed + 1000), PH, 150, burn=(50, 6000)):
        cur = y
        for n in range(40):
            a = phi(cur)
            nxt = S3(cur)
            b = phi(nxt)
            if a is None or b is None:
                unseen += 1
                break
            a2 = a.copy(); S(a2)
            if same(a2, b, R_EQ) and inY(a):
                ok += 1
            else:
                bad += 1
            cur = nxt
    print(f'validation phi(S^3 y) = S phi(y): ok {ok}, bad {bad}, unseen-window stops {unseen}')
    # bijectivity: for random z in Y, count y in A (insertion candidates) with phi(y) = z
    counts = collections.Counter()
    rng2 = random.Random(seed + 2000)
    for _ in range(300):
        z = rand_conf(rng2, rng2.randrange(50, 3000))
        sols = set()
        for j in range(-D - 1, D + 2):
            for a in range(3):
                for hs in range(-D - 1, D + 2):
                    for sh in 'bdpq':
                        cells = [z.cell(z.h + i) for i in range(-W, W + 1)]
                        hi = W
                        cells.insert(hi + j, a)
                        if j < 0:
                            hi += 1
                        t = {i - hi - hs: v for i, v in enumerate(cells)}
                        y = Conf(t, 0, sh, 2, z.rng)
                        if not inY(y) or PH.get(window(y, 1)) != 0:
                            continue
                        p = phi(y)
                        if p is not None and same(p, z, R_EQ):
                            sols.add(sig(y))
        counts[len(sols)] += 1
    print('preimage counts over 300 random z in Y (insertion search):', dict(counts))
    print('rule table (window -> (del offset, head shift, shape)):')
    for w in sorted(rule):
        print(' ', w[0], ''.join(map(str, w[1])), '->', rule[w], ' alternatives', len(C[w]))


if __name__ == '__main__':
    main()
