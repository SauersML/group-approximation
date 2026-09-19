#!/usr/bin/env python3
"""Coprime speed-up test for SMART induced on Y (S = first return to genuine level-0 moves).

Question: is there a bounded edit psi (delete/insert/keep one cell within distance D of the
head, head shift in [-D,D], any phase-2 shape) with psi(S^q y) = S(psi(y))?

POINTWISE SOUND TEST: for a given y, psi(y) must be SOME edit e1(y) and psi(S^q y) must be SOME
edit e2(S^q y).  If no pair (e1, e2) satisfies e2(S^q y) == S(e1(y)) (compared within radius
R_EQ on fully materialised tapes, which is only a NECESSARY condition for equality), then no
psi in the class, with any window rule whatsoever, satisfies the identity at y.

Controls: q = 3 restricted to A (the known height-3 renormalization, must never be refuted);
q = 3 on all of Y (globally impossible: S^3 preserves A, so it is not minimal, while S is).
q = 2 on all of Y is impossible iff -1 is an eigenvalue of S, which is not established.
Test: q = 5, 7.
"""
import random, sys, collections

MOVE = {'b': 1, 'p': 1, 'd': -1, 'q': -1}
RW = {
    ('b', 0): (1, 'd'), ('b', 1): (1, 'q'), ('b', 2): (2, 'q'),
    ('d', 0): (1, 'b'), ('d', 1): (1, 'p'), ('d', 2): (2, 'p'),
    ('p', 0): (2, 'b'), ('p', 1): (0, 'b'), ('p', 2): (0, 'q'),
    ('q', 0): (2, 'd'), ('q', 1): (0, 'd'), ('q', 2): (0, 'p'),
}
D = 2
R_EQ = 40
MARGIN = 60


class Edge(Exception):
    pass


def step(c):
    t, h, s, ph = c
    if ph == 2:
        h += MOVE[s]
        if h < MARGIN or h > len(t) - MARGIN:
            raise Edge()
        return [t, h, s, 1]
    w, ns = RW[(s, t[h])]
    t[h] = w
    return [t, h, ns, 2]


def inY(c):
    t, h, s, ph = c
    if ph != 2:
        return False
    if s in 'bd':
        return t[h] != 0
    if s == 'p':
        return t[h + 1] != 0
    return t[h - 1] != 0


def inA(c):
    t, h, s, ph = c
    if ph != 2:
        return False
    if s == 'b':
        return (t[h] != 0 and t[h + 1] == 0) or (t[h] == 2 and t[h + 1] != 0)
    if s == 'd':
        return (t[h] != 0 and t[h - 1] == 0) or (t[h] == 2 and t[h - 1] != 0)
    return False


def S(c):
    n = 0
    while True:
        c = step(c)
        n += 1
        if inY(c):
            return c
        if n > 50:
            raise RuntimeError('return > 50')


def clone(c):
    return [c[0][:], c[1], c[2], c[3]]


def Sk(c, k):
    c = clone(c)
    for _ in range(k):
        c = S(c)
    return c


def sig(c):
    t, h, s, ph = c
    return (s, ph, tuple(t[h - R_EQ:h + R_EQ + 1]))


def edits(c):
    t, h, s, ph = c
    ops = [('id', 0, None)] + [('del', j, None) for j in range(-D, D + 1)] \
        + [('ins', j, a) for j in range(-D, D + 1) for a in range(3)]
    out = []
    for op, j, a in ops:
        tt = t[:]
        hh = h
        if op == 'del':
            del tt[h + j]
            if j < 0:
                hh -= 1
        elif op == 'ins':
            tt.insert(h + j, a)
            if j < 0:
                hh += 1
        for hs in range(-D, D + 1):
            for sh in 'bdpq':
                z = [tt, hh + hs, sh, 2]
                if inY(z):
                    out.append(z)
    return out


def pair_ok(y, q):
    """exists e1, e2 in the class with e2(S^q y) == S(e1(y)) (within R_EQ)?"""
    left = set()
    for z in edits(y):
        try:
            left.add(sig(S(clone(z))))
        except Edge:
            pass
    yq = Sk(y, q)
    for z in edits(yq):
        if sig(z) in left:
            return True
    return False


def samples(rng, n, L, p0, needA):
    out = []
    while len(out) < n:
        t = [0 if rng.random() < p0 else rng.choice((1, 2)) for _ in range(L)]
        c = [t, L // 2, rng.choice('bdpq'), 2]
        try:
            while not inY(c):
                c = step(c)
            for _ in range(rng.randrange(0, 3000)):
                c = S(c)
            if needA:
                while not inA(c):
                    c = S(c)
            out.append(c)
        except Edge:
            pass
    return out


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 21
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    rng = random.Random(seed)
    L = 700
    for p0 in (1 / 3, 0.9):
        YA = samples(rng, n, L, p0, needA=True)
        Yall = samples(rng, n, L, p0, needA=False)
        rows = [('q=3 on A (control, must pass)', YA, 3),
                ("q=2 on Y (status open)", Yall, 2),
                ("q=3 on Y (impossible)", Yall, 3),
                ('q=5 on Y (test)', Yall, 5),
                ('q=7 on Y (test)', Yall, 7)]
        for name, ys, q in rows:
            ok = bad = edge = 0
            for y in ys:
                try:
                    if pair_ok(y, q):
                        ok += 1
                    else:
                        bad += 1
                except Edge:
                    edge += 1
            print(f'p0 {p0:.2f}  {name:34s} points with a matching edit pair: {ok}/{ok + bad}'
                  f'  (refuted at {bad}; edge {edge})', flush=True)


if __name__ == '__main__':
    main()
