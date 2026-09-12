---
rg: 2
id: measure-conjugacy-invariants-cannot-certify-surjectivity
kind: claim
title: Isomorphism invariants of the image action cannot separate an injective automaton's image measure from the Bernoulli measure
distinct_from:
  kazhdan-bernoulli-rigidity-forces-surjective-embeddings: that is a refuted rigidity architecture over simple Kazhdan groups and coset shifts; this proves over every group and for every isomorphism invariant that the image measure and the uniform Bernoulli measure are indistinguishable by invariants, so no invariant comparison can certify surjectivity.
  injective-measure-preserving-ca-is-surjective: that proves an injective automaton that preserves the uniform measure is surjective; this proves that invariants of the image action's isomorphism class cannot detect whether the image measure is the uniform one.
  every-injective-ca-preserves-uniform-bernoulli-measure: that is the open all-groups preservation hypothesis equivalent to the goal; this constrains what kind of argument could establish it.
artifacts:
  - research/artifacts/conjugacy-invariants-and-partition-bounds-2026-09-12.md
---

Let `G` be a countable group, `A` a finite alphabet, `mu` the uniform product measure on `A^G`,
`tau` an injective cellular automaton, and `nu = tau_* mu`.

Then `tau` is an isomorphism of measure-preserving actions `G ↷ (A^G, mu) -> G ↷ (A^G, nu)`, and
a topological conjugacy of `A^G` onto the subshift `tau(A^G)`. Consequently:
- every isomorphism invariant of measure-preserving `G`-actions takes the same value on `nu` as on
  `mu`. That includes Koopman spectral data, strong ergodicity, spectral gap, mixing of all orders,
  weak equivalence, cost and `l^2`-Betti numbers of the orbit relation, cocycle-superrigidity
  properties, and every entropy invariant;
- every conjugacy invariant of `G`-subshifts takes the same value on `tau(A^G)` as on `A^G`.

So a property of invariant measures that holds for `mu` and fails for every strict image must depend
on the coordinate structure of `A^G`, not only on the isomorphism class of the action. Of the data
such a proof can use, the artifact names four types:
- window laws of the coordinate partition;
- completion counts of the image shift of finite type;
- block-code radii of the automaton and its decoder;
- the group structure of the index set.

The tree calibration `end-fixing-tree-symmetries-carry-strict-automata` shows the first three are
not enough.

Proof: Section 1 of the linked artifact. It is elementary: `tau` is a continuous equivariant
injection of a compact space.
