---
rg: 2
id: implemented-corona-actions-unconstrained-proof
kind: route
title: Solve the finitely many invariance equations in positive integers level by level and permute blocks
target: implemented-corona-actions-of-countable-groups-are-unconstrained
requires: []
---

## Proof

The complete proof is the `## Proof` section of the target claim.
- At level `n`, the invariant measure is a strictly positive real solution of
  finitely many rational linear equations.  Rational points are dense in the
  solution space, so a strictly positive integer solution gives block ranks.
- Diagonal block projections give an isometric embedding of `C(X)` into the
  corona.
- Equal block ranks give permutation unitaries.  These implement each group
  element on all clopen sets of the coarser partitions, exactly for large `n`.
- The implementing cocycle lies in the relative commutant.
- For the no-go, the Bernoulli shift on `({0,1}^N)^G` with product measure
  is a nontrivial full-support invariant action for every nontrivial
  countable `G`.
