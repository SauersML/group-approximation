#!/usr/bin/env python3
"""SMART induced on genuine level-0 moves (Y): phase parsing, Z/3 readability, and a
bounded-edit search for a height-3 renormalization phi with phi S^3 = S phi.

Table: Callard--Salo arXiv:2208.00685v3, distortion-1-smart.tex, tikz figure.
Shapes b(▶) d(◀) p(⊳) q(⊲); phase 2 moves (b,p right; d,q left) and enters phase 1;
phase 1 reads/writes and enters a phase-2 state.
Y = phase-2 configs: b,d on a nonzero cell; p with nonzero right neighbour; q with
nonzero left neighbour.  S = first-return map to Y.
Substitution (lane gq-nv-obstruct): b->bdp, d->dbq, p->bqp, q->dpq.
"""
import random, sys, collections

MOVE = {'b': 1, 'p': 1, 'd': -1, 'q': -1}
RW = {  # (shape, read) -> (write, new shape)   [new phase is 2]
    ('b', 0): (1, 'd'), ('b', 1): (1, 'q'), ('b', 2): (2, 'q'),
    ('d', 0): (1, 'b'), ('d', 1): (1, 'p'), ('d', 2): (2, 'p'),
    ('p', 0): (2, 'b'), ('p', 1): (0, 'b'), ('p', 2): (0, 'q'),
    ('q', 0): (2, 'd'), ('q', 1): (0, 'd'), ('q', 2): (0, 'p'),
}
SIGMA = {'b': 'bdp', 'd': 'dbq', 'p': 'bqp', 'q': 'dpq'}
SIGINV = {v: k for k, v in SIGMA.items()}
PAD = 0  # cells outside the stored window read as random (filled lazily)


class Conf:
    """tape: dict pos->symbol (lazy random fill), head pos, shape, phase."""
    __slots__ = ('t', 'h', 's', 'ph', 'rng')

    def __init__(self, t, h, s, ph, rng):
        self.t, self.h, self.s, self.ph, self.rng = t, h, s, ph, rng

    def cell(self, i):
        v = self.t.get(i)
        if v is None:
            v = self.rng.randrange(3)
            self.t[i] = v
        return v

    def copy(self):
        return Conf(dict(self.t), self.h, self.s, self.ph, self.rng)


def step(c):
    if c.ph == 2:
        c.h += MOVE[c.s]
        c.ph = 1
    else:
        w, ns = RW[(c.s, c.cell(c.h))]
        c.t[c.h] = w
        c.s, c.ph = ns, 2


def inY(c):
    if c.ph != 2:
        return False
    if c.s in 'bd':
        return c.cell(c.h) != 0
    if c.s == 'p':
        return c.cell(c.h + 1) != 0
    return c.cell(c.h - 1) != 0


def S(c):
    """advance c in place to the next Y-visit (first return); returns number of F-steps."""
    n = 0
    while True:
        step(c)
        n += 1
        if inY(c):
            return n
        if n > 50:
            raise RuntimeError('return time exceeded 50')


def letters(c, n):
    c = c.copy()
    out = []
    for _ in range(n):
        out.append(c.s)
        S(c)
    return ''.join(out)


def offsets(L):
    """offsets o in {0,1,2} such that every full triple L[o+3i:o+3i+3] is a sigma-image."""
    ok = []
    for o in range(3):
        good = True
        for i in range(o, len(L) - 2, 3):
            if L[i:i + 3] not in SIGINV:
                good = False
                break
        if good:
            ok.append(o)
    return ok


def window(c, r):
    return (c.s, tuple(c.cell(c.h + i) for i in range(-r, r + 1)))


def rand_conf(rng, burn):
    c = Conf({}, 0, rng.choice('bdpq'), rng.choice((1, 2)), rng)
    while not inY(c):
        step(c)
    for _ in range(burn):
        S(c)
    for i in range(-400, 401):  # prefill so copies share the same finite tape
        c.cell(c.h + i)
    return c


def same(c1, c2, R):
    """equal as configurations within radius R of the head (tape relative to head)."""
    if c1.s != c2.s or c1.ph != c2.ph:
        return False
    return all(c1.cell(c1.h + i) == c2.cell(c2.h + i) for i in range(-R, R + 1))
