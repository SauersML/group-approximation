---
rg: 2
id: no-absorption-from-dual-surjunctivity
kind: route
title: The first coordinate of an absorption is post-surjective and not pre-injective, so dual surjunctivity forbids absorptions
target: no-group-carries-a-topological-bernoulli-absorption
requires:
  - every-group-is-dual-surjunctive
  - absorptions-give-post-surjective-strict-pairs
---

If `Psi : A^G -> A^G x Y` is an absorption, then by (i) of `absorptions-give-post-surjective-strict-pairs`,
`pr_1 Psi` is a post-surjective cellular automaton on `A^G` that is not pre-injective.
`every-group-is-dual-surjunctive` says every post-surjective automaton over every group is pre-injective.
