---
rg: 2
id: fp-simple-amenable-via-hyde-lodha-group
kind: route
title: "Dead: Hyde–Lodha's finitely presented simple group Q_2 as the example"
target: fp-infinite-simple-amenable-group
requires: []
---

**Dead.** Invalidated by `hyde-lodha-periodic-simple-groups-are-not-amenable`, whose
own proof route is complete, so this route never fires.

**The candidate.** `Q_2 = [Γ_2, Γ_2]` is a finitely presented simple group of
orientation-preserving homeomorphisms of `R`, of type `F_∞` (Hyde–Lodha, Theorems 1.3
and 4.8). It is infinite and torsion-free. So it contains no copy of Thompson's `V`,
it is not a lattice in a product of trees, and none of the region's earlier
obstructions applied to it.

**Why it dies.** `Γ_2` commutes with `t -> t + 1` and so acts on the circle. The
periodic copy of `F_6'` inside `Q_2` compresses arcs, which leaves the atom at `0̄` as
the only candidate invariant probability measure, and some element of `Q_2` moves
`0̄`. An amenable `Q_2` would need an invariant probability measure on the circle.
