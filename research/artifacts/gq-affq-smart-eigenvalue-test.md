# Locally readable eigenvalues of induced SMART (lane gq-affq, 2026-09-18)

`S` is SMART induced on the genuine level-0 moves `Y`
(`smart-induced-on-genuine-moves-has-exact-tripling`). For `n = 2, 3, 4` and each radius `r`, the
test asks whether some `χ: {radius-r windows} -> Z/n` satisfies `χ(S y) = χ(y) + 1` along sampled
orbits. It builds a constraint graph on the windows seen, with an edge labelled `+1` from each
window to the next, and checks with an offset union-find that every cycle sums to `0 mod n`.
- A **conflict (X)** proves that no eigenfunction for `e^{2πi/n}` is a function of the radius-`r`
  window.
- **ok** only means no cycle contradicted it. At large `r` windows rarely repeat, so ok is then
  uninformative.

MSI, single core, python3, seed 5: 60 tapes of length 6000 with `P(0)` in `{1/3, 0.5, 0.9}`,
4000 `S`-steps each.

| eigenvalue | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7–r12 |
|---|---|---|---|---|---|---|---|---|
| `e^{2πi/2} = -1` | ok | ok | ok | ok | ok | ok | ok | ok |
| `e^{2πi/3}` | X | ok | ok | ok | ok | ok | ok | ok |
| `e^{2πi/4} = i` | X | X | X | X | X | X | X | ok (uninformative) |

**Reading.**
- *`-1`.* It is consistent already at radius 0, so the eigenfunction reads only the state. It is
  the head direction, and `smart-induced-map-alternates-head-direction` proves this by hand from
  the table.
- *`e^{2πi/3}`.* It needs radius 1. This matches the known `Z_3` factor and calibrates the test.
- *`i`.* No `Z/4` eigenfunction reads a window of radius at most 6. A height-2 renormalization of
  `S` would need one at some finite radius (`smart-induced-map-alternates-head-direction`, item 2).
  This is evidence against SMART as a `BS(1,2)` base, not a proof.

## Script (`smart_eig.py`)

```python
#!/usr/bin/env python3
"""Is exp(2 pi i / n) a continuous eigenvalue of S (SMART induced on genuine level-0 moves Y),
with an eigenfunction readable from the radius-r window at the head?

chi: windows -> Z/n with chi(S y) = chi(y) + 1.  Constraint graph: nodes = radius-r windows seen,
edge W(S^j y) -> W(S^{j+1} y) with label +1.  chi exists (on the sampled windows) iff every cycle
has total label 0 mod n; checked by union-find with offsets.  A conflict at radius r means no
eigenfunction for exp(2 pi i/n) is a function of the radius-r window (necessary-condition test;
a larger radius could still work).  Calibration: n = 3 must be consistent (known Z_3 factor)."""
import random, sys

MOVE = {'b': 1, 'p': 1, 'd': -1, 'q': -1}
RW = {
    ('b', 0): (1, 'd'), ('b', 1): (1, 'q'), ('b', 2): (2, 'q'),
    ('d', 0): (1, 'b'), ('d', 1): (1, 'p'), ('d', 2): (2, 'p'),
    ('p', 0): (2, 'b'), ('p', 1): (0, 'b'), ('p', 2): (0, 'q'),
    ('q', 0): (2, 'd'), ('q', 1): (0, 'd'), ('q', 2): (0, 'p'),
}
MARGIN = 30


class Edge(Exception):
    pass


def step(t, h, s, ph):
    if ph == 2:
        h += MOVE[s]
        if h < MARGIN or h > len(t) - MARGIN:
            raise Edge()
        return h, s, 1
    w, ns = RW[(s, t[h])]
    t[h] = w
    return h, ns, 2


def inY(t, h, s, ph):
    if ph != 2:
        return False
    if s in 'bd':
        return t[h] != 0
    if s == 'p':
        return t[h + 1] != 0
    return t[h - 1] != 0


class UF:
    """offset union-find: off[x] = chi(x) - chi(parent(x)) mod n; union by size."""
    def __init__(self, n):
        self.p, self.off, self.sz, self.n = {}, {}, {}, n

    def find(self, x):
        if x not in self.p:
            self.p[x], self.off[x], self.sz[x] = x, 0, 1
        o = 0
        while self.p[x] != x:
            o += self.off[x]
            x = self.p[x]
        return x, o % self.n

    def union(self, a, b, d):
        """require chi(b) = chi(a) + d; return False on conflict."""
        ra, oa = self.find(a)
        rb, ob = self.find(b)
        if ra == rb:
            return (ob - oa - d) % self.n == 0
        # chi(b) = chi(rb) + ob, chi(a) = chi(ra) + oa; need chi(rb) - chi(ra) = oa + d - ob
        k = (oa + d - ob) % self.n
        if self.sz[ra] < self.sz[rb]:
            self.p[ra], self.off[ra] = rb, (-k) % self.n
            self.sz[rb] += self.sz[ra]
        else:
            self.p[rb], self.off[rb] = ra, k
            self.sz[ra] += self.sz[rb]
        return True


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    ntapes = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
    rng = random.Random(seed)
    radii = list(range(0, 13))
    tests = {(n, r): [UF(n), True] for n in (2, 3, 4) for r in radii}
    for _ in range(ntapes):
        L = 6000
        p0 = rng.choice((1 / 3, 0.5, 0.9))
        t = [0 if rng.random() < p0 else rng.choice((1, 2)) for _ in range(L)]
        h, s, ph = L // 2, rng.choice('bdpq'), 2
        try:
            while not inY(t, h, s, ph):
                h, s, ph = step(t, h, s, ph)
            prev = None
            for j in range(steps):
                win = {r: (s,) + tuple(t[h - r:h + r + 1]) for r in radii}
                if prev is not None:
                    for (n, r), v in tests.items():
                        if v[1] and not v[0].union(prev[r], win[r], 1):
                            v[1] = False
                prev = win
                h, s, ph = step(t, h, s, ph)
                while not inY(t, h, s, ph):
                    h, s, ph = step(t, h, s, ph)
        except Edge:
            pass
    for n in (2, 3, 4):
        row = ' '.join(f'r{r}:{"ok" if tests[(n, r)][1] else "X"}' for r in radii)
        print(f'exp(2pi i/{n}):  {row}')


if __name__ == '__main__':
    main()
```
