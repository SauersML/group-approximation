# Validation of the brick-local height-3 renormalization of induced SMART (lane gq-affq, 2026-09-18)

**Claim checked.** `smart-induced-map-has-brick-local-height-3-renormalization` (lane
gq-nv-obstruct, landed OPEN 9fadf5ac6). `S` is SMART's moving-tape map induced on `Y`, the
genuine level-0 moves (`smart-induced-on-genuine-moves-has-exact-tripling`). `A ⊆ Y` is the set
of first `Y`-points of level-1 moves, and `φ: A -> Y` is:
- `▶_2` on a nonzero cell with right neighbour `0`: delete that `0`, keep `▶_2`;
- `◀_2` on a nonzero cell with left neighbour `0`: delete that `0`, keep `◀_2`;
- `▶_2` on a `2` with nonzero right neighbour: delete the head cell, head onto the left
  neighbour, state `⊳_2`;
- `◀_2` on a `2` with nonzero left neighbour: delete the head cell, head onto the right
  neighbour, state `⊲_2`.

Each case is a bounded prefix replacement in the moving-tape coding, so `φ` is brick-local.

**What was tested** (MSI only, single core, python3, fixed seeds; script below):
1. **Intertwining** `φ(S^3 y) = S(φ(y))` at every `A`-point along long orbits. Configurations
   are full finite Python lists derived from one random tape. Comparison is of the **whole common
   array relative to the head** (a 25-cell margin at each end), not a bounded radius. No lazily
   drawn cells are used, so the harness bug of the first search cannot recur.
2. **Tower:** after an `A`-point, the next `A`-point is exactly 3 `Y`-visits later, and neither of
   the two intermediate visits is in `A`. So `Y = A ⊔ SA ⊔ S^2A` and `S^3 A = A` along every orbit.
3. **Bijectivity:** for random `z ∈ Y`, the explicit inverse (insert `0` or `2` next to the head,
   with the matching state change) lands in `A`, and `φ` maps it back to `z`.

**Results.** No failures of any kind.

| seed | P(cell = 0) | tapes | tape length | A-points per tape | `φ S^3 = S φ` | tower failures | inverse checks |
|---|---|---|---|---|---|---|---|
| 11 | 1/3 | 40 | 3000 | 400 | 16000 / 16000 | 0 | 1993 / 1993 |
| 12 | 0.90 | 40 | 3000 | 300 | 12000 / 12000 | 0 | 2020 / 2020 |
| 13 | 0.97 | 40 | 3000 | 300 | 12000 / 12000 | 0 | 2010 / 2010 |
| 14 | 0.50 | 30 | 4000 | 500 | 15000 / 15000 | 0 | 2046 / 2046 |

Total: **55,000** intertwining checks and **8,069** inverse checks pass, with no edge stops (the
head never reached the tape margins). At `P(0) = 0.97` the zero blocks have length about 33, so
high-level moves are exercised.

**What this is and is not.** It is strong corroboration for all finite-level behaviour on
typical tapes. It is **not a proof**: the identity must hold on every configuration of the
Cantor space, including limiting ones, such as configurations inside an infinite zero block or an
all-`⊳`/all-`⊲` chain, where `y` and `S^3 y` share no finite move. gq-nv-obstruct's inductive
proof, plus density and continuity for those, is what referees must check. If it holds, then
`renormalizable-thompson-elements-give-baumslag-solitar` (with `brin-thompson-first-return-maps-lie-in-kv`
to move `S` into `2V`) gives `BS(1,3) <= 3V`.

## Script (`smart_phi_exact.py`)

Run as `python3 smart_phi_exact.py <seed> <tapes> <length> <A-points per tape> <P(0)>`.

```python
#!/usr/bin/env python3
"""Validate gq-nv-obstruct's explicit height-3 renormalization of SMART induced on Y,
on FULL finite tapes (no lazy cells): phi(S^3 y) == S(phi(y)) as whole arrays relative to
the head, A = Y-points that are the first Y-point of a level-1 move, and the tower
Y = A u SA u S^2A (A-visits every third Y-visit).

Tape: a Python list of symbols; a config is (tape list, head index, shape, phase).
All configs derived from one random tape by the machine and by phi; comparisons use the
whole common range relative to the head."""
import random, sys, collections

MOVE = {'b': 1, 'p': 1, 'd': -1, 'q': -1}
RW = {
    ('b', 0): (1, 'd'), ('b', 1): (1, 'q'), ('b', 2): (2, 'q'),
    ('d', 0): (1, 'b'), ('d', 1): (1, 'p'), ('d', 2): (2, 'p'),
    ('p', 0): (2, 'b'), ('p', 1): (0, 'b'), ('p', 2): (0, 'q'),
    ('q', 0): (2, 'd'), ('q', 1): (0, 'd'), ('q', 2): (0, 'p'),
}
MARGIN = 50


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
    t[h] = w  # in place; phi copies the tape it needs
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


def S(c):
    n = 0
    while True:
        c = step(c)
        n += 1
        if inY(c):
            return c
        if n > 50:
            raise RuntimeError('return > 50')


def inA(c):
    t, h, s, ph = c
    if ph != 2:
        return False
    if s == 'b':
        return (t[h] != 0 and t[h + 1] == 0) or (t[h] == 2 and t[h + 1] != 0)
    if s == 'd':
        return (t[h] != 0 and t[h - 1] == 0) or (t[h] == 2 and t[h - 1] != 0)
    return False


def phi(c):
    t, h, s, ph = c
    assert ph == 2
    if s == 'b' and t[h] != 0 and t[h + 1] == 0:      # start of M_b(1): delete right 0
        return [t[:h + 1] + t[h + 2:], h, 'b', 2]
    if s == 'd' and t[h] != 0 and t[h - 1] == 0:      # start of M_d(1): delete left 0
        return [t[:h - 1] + t[h:], h - 1, 'd', 2]
    if s == 'b' and t[h] == 2 and t[h + 1] != 0:      # first Y-point of M_p(1)
        return [t[:h] + t[h + 1:], h - 1, 'p', 2]
    if s == 'd' and t[h] == 2 and t[h - 1] != 0:      # first Y-point of M_q(1)
        return [t[:h] + t[h + 1:], h, 'q', 2]
    return None


def same(c1, c2):
    t1, h1, s1, p1 = c1
    t2, h2, s2, p2 = c2
    if s1 != s2 or p1 != p2:
        return False
    lo = min(h1, h2) - MARGIN // 2
    hi = min(len(t1) - h1, len(t2) - h2) - MARGIN // 2
    return t1[h1 - lo:h1 + hi] == t2[h2 - lo:h2 + hi]


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    ntapes = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    L = int(sys.argv[3]) if len(sys.argv) > 3 else 3000
    steps = int(sys.argv[4]) if len(sys.argv) > 4 else 400
    p0 = float(sys.argv[5]) if len(sys.argv) > 5 else 1/3
    rng = random.Random(seed)
    stat = collections.Counter()
    tower_bad = 0
    for k in range(ntapes):
        t = [0 if rng.random() < p0 else rng.choice((1, 2)) for _ in range(L)]
        c = [t, L // 2, rng.choice('bdpq'), 2]
        try:
            while not inY(c):
                c = step(c)
            for _ in range(rng.randrange(0, 5000)):   # burn-in along the orbit
                c = S(c)
            # align to an A point
            k0 = 0
            while not inA(c):
                c = S(c)
                k0 += 1
                if k0 > 10:
                    raise RuntimeError('no A point within 10 Y-steps')
            # walk: check tower period 3 and the intertwining at every A point
            for n in range(steps):
                z = phi(c)  # copies the tape
                Sz = S(z) if (z is not None and inY(z)) else None
                c = S(c); a1 = inA(c)
                c = S(c); a2 = inA(c)
                c = S(c); a3 = inA(c)
                if a1 or a2 or not a3:
                    tower_bad += 1
                if Sz is None:
                    stat["phi-not-in-Y"] += 1
                else:
                    z3 = phi(c)
                    if z3 is not None and same(Sz, z3):
                        stat["ok"] += 1
                    else:
                        stat["BAD"] += 1
        except Edge:
            stat['edge-stop'] += 1
    print(f"p0 {p0:.2f} "+f"seed {seed} tapes {ntapes} L {L} steps {steps}: {dict(stat)} tower_bad {tower_bad}")
    # bijectivity: phi: A -> Y has the explicit inverse; check phi(psi(z)) == z and psi(z) in A
    bij = collections.Counter()
    for _ in range(3000):
        t = [rng.randrange(3) for _ in range(400)]
        s = rng.choice('bdpq')
        z = [t, 200, s, 2]
        if not inY(z):
            continue
        tz, h = z[0], z[1]
        if s == 'b':
            y = [tz[:h + 1] + [0] + tz[h + 1:], h, 'b', 2]
        elif s == 'd':
            y = [tz[:h] + [0] + tz[h:], h + 1, 'd', 2]
        elif s == 'p':
            y = [tz[:h + 1] + [2] + tz[h + 1:], h + 1, 'b', 2]
        else:
            y = [tz[:h] + [2] + tz[h:], h, 'd', 2]
        good = inA(y) and phi(y) is not None and same(phi(y), z)
        bij['inverse-ok' if good else 'inverse-FAIL'] += 1
    print('bijectivity (explicit inverse on random z in Y):', dict(bij))


if __name__ == '__main__':
    main()
```
