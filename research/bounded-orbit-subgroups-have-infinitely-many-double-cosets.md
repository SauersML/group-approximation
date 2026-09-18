---
rg: 2
id: bounded-orbit-subgroups-have-infinitely-many-double-cosets
kind: claim
title: A subgroup with a bounded orbit in an isometric action that has an unbounded orbit has infinitely many double cosets, and a commensurated subgroup with finitely many double cosets has finite index
distinct_from:
  fp-clopen-transitive-full-cantor-groups-have-type-a-actions: that produces type (A) actions with finitely many pair orbits; this gives two elementary necessary conditions on the point stabilizer of any action with finitely many orbits of pairs.
  commensurator-rigid-groups-have-no-faithful-bs-members: that obstructs BLIW hosts, whose vertex groups are commensurated; item 2 here shows the point stabilizers of an infinite transitive action with finitely many pair orbits are never commensurated, so the two host methods need opposite subgroups.
---

**ESTABLISHED** (lane proof, elementary, inline below; not reviewed; no priority
claimed, both statements are standard-looking folklore).

Let `G` be a group and `H ≤ G` a subgroup. Finitely many double cosets
`H\G/H` is the same as finitely many `G`-orbits on ordered pairs of `G/H`.

1. **Bounded orbits.** Suppose `G` acts by isometries on a metric space `X`,
   some `G`-orbit is unbounded, and `H` has a bounded orbit. Then `H\G/H` is
   infinite.
2. **Commensurated subgroups.** If `H` is commensurated in `G` (every
   `H ∩ gHg⁻¹` has finite index in `H`) and `H\G/H` is finite, then `[G:H]` is
   finite.

**Proof of 1.** Pick `x ∈ X` with `Hx` of diameter `D < ∞`. Every orbit of an
isometric action is unbounded if one is, so `sup_g d(x,gx) = ∞`. For
`g' = hgh'` with `h, h' ∈ H`,
`|d(x,g'x) − d(x,gx)| = |d(h⁻¹x, gh'x) − d(x,gx)| ≤ d(h⁻¹x,x) + d(gh'x,gx) ≤ 2D`.
So on each double coset the function `g ↦ d(x,gx)` takes values in an interval
of length `4D`. Finitely many double cosets would make it bounded.

**Proof of 2.** Commensuration means the `H`-orbit of `gH` in `G/H` is finite,
of size `[H : H ∩ gHg⁻¹]`. So each double coset `HgH` is a finite union of left
cosets, and `G = ⋃_{i ≤ k} Hg_iH` makes `G/H` finite.

**Use.** In a faithful action with finitely many orbits of ordered pairs of an
infinite group, some point orbit `G/H` is infinite and `H\G/H` is finite. So by
1, `H` has unbounded orbits in every isometric action of `G` with an unbounded
orbit, and by 2, `H` is not commensurated. The first is the working constraint
in `out-free-pair-finite-stabilizers-contain-fully-irreducibles`.

**Calibration.** For a lattice `Γ` acting on a tree, a vertex stabilizer has a
bounded orbit, and `Γ` has infinitely many orbits on vertex pairs (their distance
is an invariant). A boundary-point stabilizer, as in the highly transitive
Burger–Mozes actions (`burger-mozes-simple-lattices-are-highly-transitive`), has
unbounded orbits on the tree, as item 1 requires.
