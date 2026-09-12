---
rg: 2
id: leavitt-unit-group-has-only-trivial-sofic-morphisms
kind: claim
title: Every homomorphism from the binary Leavitt unit group to a universal sofic group is trivial
distinct_from:
  openai-leavitt-unit-nonsofic: that says the unit group admits no injective sofic morphism; this says every sofic morphism is trivial, equivalently the sofic radical is the whole group, which uses simplicity on top of nonsoficity.
  binary-leavitt-all-ranks-full-mf-radical: that kills the unit group in every operator-norm approximate representation; this kills it in every almost-multiplicative permutation model, with collisions allowed.
artifacts:
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

Let `R = L_(F_2)(1,2)`. Then `Rad(R^x) = R^x`, with the sofic radical of
`sofic-radical-localizes-garden-of-eden-windows`. Equivalently:

- every homomorphism from `R^x` to a metric ultraproduct of symmetric groups is
  trivial;
- finitarily, for every finite set `E` of nontrivial elements and `eps > 0`
  there is a scale `(F, delta)` at which every almost-multiplicative permutation
  model fixes each element of `E` on all but an `eps`-fraction of points.

The same holds for `EL_n(R)`, `n >= 3`, which are isomorphic to `R^x`.

**Consequence for Gottschalk.** In the Gromov--Weiss counting every
Garden-of-Eden chart collapses at density tending to one. The localization
theorem therefore imposes no condition on a strict automaton over `R^x` whose
memory generates `R^x`. By
`invariant-output-injective-automata-need-invisible-symmetry`, every finite
subgroup is an admissible symmetry for a coset-invariant output. This is the
precise sense in which the counting step of Gromov--Weiss fails over the
binary Leavitt unit group.
