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


def edits(c, d):
    """bounded local edits of a phase-2 config: optional deletion of one cell at offset
    j in [-d,d] or insertion of a symbol at offset j, then head offset h in [-d,d], new
    shape; result kept only if in Y."""
    out = []
    base_ops = [('id', 0, None)]
    base_ops += [('del', j, None) for j in range(-d, d + 1)]
    base_ops += [('ins', j, a) for j in range(-d, d + 1) for a in range(3)]
    for op, j, a in base_ops:
        # materialise a window, apply op, rebuild dict relative to head
        W = 150
        cells = [c.cell(c.h + i) for i in range(-W, W + 1)]
        hi = W
        if op == 'del':
            del cells[hi + j]
            if j < 0:
                hi -= 1
        elif op == 'ins':
            cells.insert(hi + j, a)
            if j < 0:
                hi += 1
        for hs in range(-d, d + 1):
            for sh in 'bdpq':
                t = {i - hi - hs: v for i, v in enumerate(cells)}
                # cells beyond the window: keep the original random tape, re-aligned
                z = Conf(t, 0, sh, 2, c.rng)
                if inY(z):
                    out.append(((op, j, a, hs, sh), z, (hi, hs)))
    return out


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    NS = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    # E1: phase-parse uniqueness and Z/3 readability of the phase from radius-r windows
    print('# E1 phase parsing (offsets valid over 300 letters)')
    stats = collections.Counter()
    phase_by_window = {r: collections.defaultdict(set) for r in range(0, 9)}
    samples = []
    for k in range(NS):
        c = rand_conf(rng, rng.randrange(200, 2000))
        L = letters(c, 300)
        o = offsets(L)
        stats[tuple(o)] += 1
        if len(o) == 1:
            # walk 60 Y-visits, record phase (index mod 3 relative to triple start)
            cc = c.copy()
            for i in range(60):
                ph = (i - o[0]) % 3
                for r in range(0, 9):
                    phase_by_window[r][window(cc, r)].add(ph)
                if ph == 0 and i < 30:
                    samples.append(cc.copy())
                S(cc)
    print('offset-sets:', dict(stats))
    for r in range(0, 9):
        tot = len(phase_by_window[r])
        bad = sum(1 for v in phase_by_window[r].values() if len(v) > 1)
        print(f'radius {r}: windows {tot}, ambiguous {bad}')
    # E2: bounded-edit search for phi on phase-0 samples
    d = 2
    NC = 25  # coarse letters to match
    print(f'# E2 edit search, d={d}, match {NC} coarse letters, {min(len(samples), 40)} samples')
    found = collections.Counter()
    nonempty = 0
    rules = []
    for y in samples[:40]:
        target = ''.join(SIGINV[letters(y, 3 * NC)[3 * i:3 * i + 3]] for i in range(NC))
        ok = []
        for key, z, _ in edits(y, d):
            if letters(z, NC) == target:
                ok.append(key)
        if ok:
            nonempty += 1
        for key in ok:
            found[key] += 1
        rules.append((window(y, 4), ok))
    print('samples with some matching edit:', nonempty, 'of', min(len(samples), 40))
    print('most common matching edits:', found.most_common(12))
    # E3: full intertwining check for each matching edit: phi(S^{3n} y) vs S^n(z)
    print("# E3 does SOME bounded edit of S^{3n} y equal S^n z (radius 20), n < 12")
    for y, (w, ok) in list(zip(samples[:40], rules))[:20]:
        if not ok:
            continue
        key = ok[0]
        z = [zz for kk, zz, _ in edits(y, d) if kk == key][0]
        yy, zz = y.copy(), z.copy()
        hits, used = 0, []
        for n in range(12):
            ks = [kk for kk, e, _ in edits(yy, d) if same(e, zz, 20)]
            if ks:
                hits += 1
                used.append(ks[0][0] + str(ks[0][1]) + "h" + str(ks[0][3]) + ks[0][4])
            else:
                used.append("NONE")
            for _ in range(3):
                S(yy)
            S(zz)
        print("window", w[0], "".join(map(str, w[1])), "edit0", key, "hits", hits, "/12", " ".join(used))
    print("done")


if __name__ == '__main__':
    main()
