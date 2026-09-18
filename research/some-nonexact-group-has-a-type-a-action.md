---
rg: 2
id: some-nonexact-group-has-a-type-a-action
kind: claim
title: Some non-exact group admits an action of type (A)
distinct_from:
  permutational-boone-higman-conjecture: that is Zaremsky's conjecture that every finitely generated decidable group embeds in a group with a type (A) action; this is its weakest instance that bites on exactness, for one non-exact group.
  fp-simple-nonexact-group: that asks for a finitely presented simple non-exact group; this implies it through twisted Brin–Thompson groups.
  osajda-decidable-nonexact-group-satisfies-boone-higman: that is Boone–Higman for Osajda's non-exact group; the permutational version for that group implies this.
---

**OPEN.** There is a non-exact group `G` with an action on a set `S` of type (A) in the sense of
`type-a-action-gives-boone-higman-for-subgroups`: faithful, `G` finitely presented, point stabilizers finitely
generated, and finitely many orbits on two-element subsets.

- **Why it matters.** It implies `fp-simple-nonexact-group`, through `fp-simple-nonexact-group-via-nonexact-type-a-actor`.
- **Sources of `G`.**
  - `permutational-boone-higman-conjecture`, applied to Osajda's decidable non-exact group
    (`decidable-residually-finite-non-exact-group-exists`), would give such a `G` containing it.
  - So would a type (A) action of any finitely presented group into which a non-exact group is Higman-embedded.
- **What is not known to work.** The type (A) actors on main that this lane checked are linear or hyperbolic,
  hence exact. Non-exactness only comes from coarsely embedded expanders or Arzhantseva–Osajda-type graphs, and
  no type (A) action of such a group is known.

## Lesson for general BH

For twisted Brin–Thompson hosts, non-exactness can be bought from the actor alone: `SV_G` is non-exact as soon as
`G` is. Whether exactness of `G` and of `V` makes `SV_G` exact is not addressed here. So the permutational route
to Boone–Higman meets the exactness diagnostic at a single point: a type (A) actor that contains an
expander-like graph.
