# Can two renormalizations of coprime heights share a base? (lane gq-affq, 2026-09-18)

**Target.** `Aff(Q)` inside an `nV` needs one copy of `(Q,+)` scaled by every prime at once.
Through the renormalization criterion (`renormalizable-thompson-elements-give-baumslag-solitar`),
that means one base `T` carrying renormalizations of every prime height, whose conjugators commute
and act on a common divisible subgroup. The first case is `Z[1/15] ⋊ ⟨×3, ×5⟩`. This note records
the first obstructions found.

## 1. Proved (`renormalization-heights-force-eigenvalue-roots`, lane proof)

- **Eigenvalue roots.** A height-`m` renormalization forces `E(T) = {μ : μ^m ∈ E(T)}`. One base
  serving every prime therefore has all roots of unity as eigenvalues and, if minimal, factors
  onto `Ẑ`.
- **Clock action.** A height-`q` renormalization acts on every `p`-adic clock (`p ∤ q`) by
  `x ↦ q^{-1}x + c`. This is a unit multiplication with unbounded carries in base-`p` digits.
- **SMART as a common base.** Only a factor of `U` onto `Z/2 × Z_3` is known. If that factor is
  maximal, `U` has no renormalization of any height with a prime factor `≠ 3`, so `U` could never
  host `×2` or `×5`.

## 2. Product bases need a coprime speed-up

In a product base `T = T_p × T_q`, a height-`p` renormalization that respects the product has
the form `φ_p × ψ`. Its second factor must satisfy `ψ ∘ T_q^p = T_q ∘ ψ`: a brick-local
conjugacy from the `p`-th power of a radix-`q` machine to the machine itself. By item 3 of the
lemma, such a `ψ` multiplies the `q`-clock by `p^{-1}`. Whether a brick-local `ψ` of this kind can
exist is the concrete test below.

## 3. MSI test on SMART's induced map `S` (single core, python3, fixed seeds)

**Class.** `ψ(y)` is a one-cell edit of `y` within distance 2 of the head (keep, delete, or
insert a symbol), with a head shift in `[-2,2]` and any phase-2 shape, landing in `Y`. This is
the class that contains the known height-3 renormalization of
`smart-induced-map-has-brick-local-height-3-renormalization`.

**Pointwise sound test.** Suppose that for some `y` no edit pair `(e_1, e_2)` in the class
satisfies `e_2(S^q y) = S(e_1(y))`. Then no `ψ` in the class, with any window rule, satisfies
`ψ S^q = S ψ` at `y`. Equality is compared within radius 40 on fully materialised tapes of length
700. That comparison is a necessary condition only, so every refutation is sound.

| tape `P(0)` | row | points with a matching pair | refuted at |
|---|---|---|---|
| 1/3 | `q = 3` on `A` (known renormalization; control) | 200/200 | 0 |
| 1/3 | `q = 2` on `Y` (status open) | 200/200 | 0 |
| 1/3 | `q = 3` on `Y` (globally impossible: `S^3` preserves `A`) | 200/200 | 0 |
| 1/3 | `q = 5` on `Y` | 199/200 | **1** |
| 1/3 | `q = 7` on `Y` | 184/200 | **16** |
| 0.9 | `q = 3` on `A` (control) | 200/200 | 0 |
| 0.9 | `q = 2` on `Y` (status open) | 200/200 | 0 |
| 0.9 | `q = 3` on `Y` (globally impossible) | 200/200 | 0 |
| 0.9 | `q = 5` on `Y` | 193/200 | **7** |
| 0.9 | `q = 7` on `Y` | 172/200 | **28** |

(The raw run printed the `q = 2` row as "impossible". That label was wrong: `S^2` fails to be
minimal only if `-1 ∈ E(S)`, which is not established. It is corrected here.)

**Reading.**
- *Weak but sound.* The globally impossible `q = 3` on `Y` is never refuted pointwise. So the
  pointwise test is weak, and "no refutation" says nothing. Each refutation, however, is sound.
- *`q = 5`, `q = 7` refuted.* No one-cell bounded edit `ψ` conjugates `S^5` or `S^7` to `S`. The
  class that carries the height-3 renormalization carries no coprime speed-up.
- *Not a general impossibility.* A `ψ` with larger edits is not excluded.

## 4. The conjectured general obstruction (not proved)

Durand, *Cobham's theorem for substitutions*, J. Eur. Math. Soc. 13 (2011) 1799–1814,
arXiv:1010.4009, states (abstract): for multiplicatively independent Perron numbers `α, β`, a
sequence over a finite alphabet that is both `α`- and `β`-substitutive is ultimately periodic.
(Read from the abstract only; not checked in the paper.)

A brick-local height-`m` renormalization makes the orbit coding of a minimal machine
self-similar for a length-`m` structure. If one aperiodic minimal base carried brick-local
renormalizations of heights `2` and `3`, and its column coding were a conjugacy, the coding would
plausibly be both `2`- and `3`-substitutive. That would contradict Durand's theorem. The
conjecture is therefore that **no single aperiodic Turing-machine-type base carries brick-local
renormalizations of multiplicatively independent heights**. The `Aff(Q)` route through `nV`
would then need a different mechanism for the dilations: the conjugators for different primes
cannot all come from renormalizing one base element `s = T × id`.

## 5. Script (`smart_speedup.py`, MSI `/projects/standard/hsiehph/sauer354/gqsrc/gq-affq/`)

```python
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
```
