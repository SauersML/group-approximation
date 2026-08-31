---
rg: 2
id: wreath-soficity-base-pair-scope-proof
kind: route
title: Read off both verdicts and check that neither embedding crosses the pairs
target: wreath-soficity-is-decided-by-the-base-pair
requires:
  - wreath-not-sofic
  - wreath-sofic-not-mf
  - a5-wreath-contains-binary-kun-thom-wreath
artifacts:
  - research/artifacts/invisible-quotients-architecture-audit-2026-08-23.md
---

Clause 1 is the first and third prerequisites.  `wreath-not-sofic` pins the
candidate to Kun--Thom's Theorem E pair explicitly -- `q` a prime power,
`r, d >= 3`, `Gamma = EL_r(R_+)`, `G = EL_r(R) x| SL_d(Z)`, compressor
`t = u_12` acting by `x_2 |-> x_1 x_2` -- and imports Theorem A for it.  The
third prerequisite puts one fixed involution of `A_5` at every site of *that*
action and concludes nonsoficity of the `A_5` lamp version by subgroup
heredity.  Its own body says "for the pinned Kun--Thom action", so its scope is
pair 1.

Clause 2 is the second prerequisite, whose group is
`L = (Z/2) wr_X V` over the affine coset space, with `V` the doubling ambient
`(Z[1/2]^3 x| SL_3(Z)) x| Z` of `doubling-quotient-residually-finite`.  Its own
body draws the contrast in as many words: the same wreath construction over the
Laurent pair is not sofic, while over the affine/doubling pair the telescope
structure restores soficity.

The scope rule is then the observation that no argument in either direction
crosses.  Nonsoficity travels *down* subgroups, so an embedding can only
transport it from a subgroup to an overgroup within one ambient action; the
sitewise-involution map is an embedding of pair-1 groups into pair-1 groups and
of pair-2 groups into pair-2 groups, and there is no homomorphism in the graph
relating the two coset spaces.  Nor would one help: soficity passes to
subgroups and to quotients only in the directions that make the two verdicts
compatible rather than transportable.

Nothing here is a new theorem; the route exists to make the identification
step, which citations cannot perform for themselves, a first-class object.
