---
rg: 2
id: kun-thom-wreath-actor-subgroups-are-not-co-amenable
kind: claim
title: In a lamp wreath over a Kazhdan actor with infinite orbits, subgroups containing the actor with infinite-orbit quotient lamps are not co-amenable
distinct_from:
  simple-kazhdan-groups-have-no-proper-co-amenable-subgroups: that is the obstruction on simple Kazhdan hosts, which have no normal subgroups; this is about wreath products, which are neither simple nor Kazhdan and carry an infinite amenable normal subgroup.
  no-invariant-mean-on-coset-space: that is the transitive coset-space statement for a Kazhdan group; this applies the same spectral argument to the affine lamp space of a wreath, where the translation invariance of the lamps kills the zero configuration.
artifacts:
  - research/artifacts/kun-thom-wreath-co-amenability-2026-09-12.md
---

**Proposition.** Let `G` have property (T), let `X` be a `G`-set with all orbits infinite, let `B` be a
nontrivial finite abelian group, and put `W = B^(X) ⋊ G`. Let `M <= B^(X)` be a proper `G`-invariant subgroup
such that every nonzero element of `B^(X)/M` has an infinite `G`-orbit. Then `M ⋊ G` is not co-amenable in `W`.

**Instances.**
- `M = 0`: the actor `G` is not co-amenable in `W`.
- For the Kun–Thom wreath with `M = N_0 = Rad_sof(W)`, the fibre-even lamps: the preimage `N_0 ⋊ G` of the
  actor in `W` is not co-amenable.
- Every co-amenable subgroup of `W` maps onto a finite-index subgroup of `G`.

**Proof idea.** `W/(M ⋊ G)` is the affine space `B^(X)/M`. A `W`-invariant mean on it is translation
invariant, so it gives the zero vector mass `0`. It is then a `G`-invariant mean on a `G`-set whose orbits
are all infinite, which property (T) forbids.

**Consequence.** Co-amenable ascent of Rokhlin maximality
(`rokhlin-maximality-ascends-co-amenable-subgroups`) cannot reach `W` from any subgroup containing the actor
of these shapes. Only subgroups with finite-orbit quotient lamps remain, and they are not classified.

**ESTABLISHED** by [[kun-thom-wreath-actor-not-co-amenable-proof]].
