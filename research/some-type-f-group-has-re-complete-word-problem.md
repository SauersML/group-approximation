---
rg: 2
id: some-type-f-group-has-re-complete-word-problem
kind: claim
title: Some group of type F has a word problem that is r.e.-complete under many-one reductions
distinct_from:
  some-type-f-group-has-unsolvable-word-problem: That gives a type F group whose word problem is not decidable; this pins its degree at the top r.e. many-one degree, which is what word-problem-degree obstructions to embeddings (Zaremsky 1.1) consume, and which unsolvability alone does not rule out.
  every-turing-degree-is-a-simple-kazhdan-lef-word-problem: That realizes every Turing degree by finitely generated (not finitely presented, not type F) simple Kazhdan LEF groups; this is one degree realized by a group of type F.
---

There is a finitely presented group `G` of type `F` (a finite `K(G,1)`) whose
word problem, the set of words over its finite generating set that represent
`1`, is complete among recursively enumerable sets under many-one reductions.

The group is the Aanderaa--Cohen--Boone group `G_M` of the machine-checked
Novikov--Boone chain, for the modular machine `M` produced there from Mathlib's
universal partial recursive function.

**Consequence.** For every finite `m`, some group of type `F_m` has an
r.e.-complete word problem. This refutes
`some-type-fm-level-has-no-complete-word-problem` at every level, so the route
`no-type-fn-plus-1-host-via-word-problem-degree` towards Zaremsky Problem 1.1
dies at its premise: many-one word-problem degree cannot separate type `F_n`
from type `F_{n+1}` hosts at any level. Every degree-based obstruction has to use
an invariant finer than the many-one degree of the word problem (for instance,
the time complexity or Dehn function, or the degree of other decision problems).

Proof: route `some-type-f-group-has-re-complete-word-problem-proof`.
