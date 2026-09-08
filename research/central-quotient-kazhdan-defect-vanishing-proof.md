---
rg: 2
id: central-quotient-kazhdan-defect-vanishing-proof
kind: route
title: Retain the per-element separating sequence and contradict Kazhdan transport
target: kazhdan-defects-vanish-in-central-quotients-of-rf-groups
requires:
  - central-quotients-of-residually-finite-groups-are-mf
  - kazhdan-asymptotic-commutant-transport
artifacts:
  - research/artifacts/central-quotient-rf-exclusion-2026-09-08.md
---

## Why sufficient

Suppose `1 != d in D_G(L)` with `L <= G` Kazhdan.  Apply the first
prerequisite to the single element `d` and **retain that individual
sequence** `W_n`, rather than the block sums used there for MF: it is an
operator-norm asymptotic representation of `G` with

```text
liminf_n ||W_n(d) - I||_2 > 0.                                     (1)
```

Now run the transport collapse in that sequence.  For `c in C_G(L)` the
matrices `W_n(c)` commute exactly with `W_n(l)` up to the multiplicative
errors, so they form a uniformly bounded Hilbert--Schmidt asymptotic
commutant of the image of `L`.  The second prerequisite, applied with the
compressor `u in Comp_G(L)` (so that conjugation by `u` carries `L` into
itself), says conjugation by the matrices representing `u` sends that
asymptotic commutant to another one.  Hence `W_n(u c u^-1)` also
asymptotically commutes with `W_n(l)` for every `l in L`, which is exactly

```text
||W_n([u c u^-1, l]) - I||_2 -> 0.                                 (2)
```

The generators of `D_G(L)` are the elements `[u c u^-1, l]` with
`u in Comp_G(L)`, `c in C_G(L)`, `l in L`, and their `G`-conjugates.
Conjugation is implemented by unitaries in each `W_n`, which preserves the
normalized Hilbert--Schmidt norm, and a product of finitely many elements
each satisfying `(2)` satisfies it too, by telescoping against the
vanishing multiplicative errors.  So `(2)` holds for every element of
`D_G(L)`, in particular for `d`, contradicting `(1)`.

Therefore no such `d` exists and `D_G(L) = {1}`.

## Scope

The analytic content is entirely the second prerequisite, consumed
unchanged; the first is elementary.  The argument uses the individual
sequences and not the MF model, which is why no comparison of dimensions
across elements is needed.  Nothing here weakens the witnesses in which a
central defect survives in an MF group: those have `L` infinite cyclic, so
the second prerequisite does not apply to them.
