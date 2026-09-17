---
rg: 2
id: kazhdan-subgroups-of-nv-act-with-finite-orbits
kind: claim
title: "Every subgroup of a Brin-Thompson group nV with property (T) has only finite orbits on C^n"
distinct_from:
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that asks for finiteness of the group; this asks only for finiteness of orbits, with no control of germs. The two are equivalent by finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite, and this form is recorded because it is purely a statement about Schreier dynamics.
  brin-thompson-groups-nv-lack-property-t: that concerns nV itself; nV has infinite orbits, so this claim implies it, but not conversely.
---

For every `n ≥ 1`, every subgroup `K ≤ nV` with property (T), and every
`x ∈ C^n`, the orbit `Kx` is finite.

## Status

- **Open for n ≥ 2.** For `n = 1` it follows from
  `thompson-v-has-haagerup-property`.
- **Equivalent to finiteness.** For Kazhdan `K` it is equivalent to
  `kazhdan-subgroups-of-brin-thompson-groups-are-finite`, by the addendum of
  `finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite`. That route
  uses only textbook facts about (T): it passes to finite-index subgroups and
  forces finite abelianization.
- **Where the germ and offset bookkeeping goes.** Once orbits are finite, the
  germ characters `Stab_K(x) → Z^n` vanish, stabilizers act trivially near their
  fixed points, and offsets are uniformly bounded. So local structure is not an
  independent obstruction.
- **Equivalent spectral form.** For every `x`, the representation `ℓ^2(Kx)`
  has almost invariant vectors.
- **What a counterexample needs.**
  - An infinite Kazhdan `K ≤ nV` must have an orbit whose Schreier graph has a
    spectral gap.
  - At a point `x` of that orbit the offset cocycle is unbounded along `K`.
  - If all coordinates of `x` are aperiodic, the offsets are differences of
    Busemann heights on the tail class. So the heights are unbounded on `Kx`.

## Attempts

- 2026-09-17 (swarm-0917-w2-zar-pull-1, operator-algebras lane): obtained the
  reduction above. No orbit bound is proved.
  - **Invariant means.** An invariant mean on an ambient `nV`-orbit, for example
    a horocyclic-product Følner sequence, gives only *some* finite `K`-orbit in
    that ambient orbit. The means need not charge a given `K`-orbit. This lane
    did not find a per-orbit version.
