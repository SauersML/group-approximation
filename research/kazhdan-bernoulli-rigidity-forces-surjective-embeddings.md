---
rg: 2
id: kazhdan-bernoulli-rigidity-forces-surjective-embeddings
kind: claim
title: Over a simple Kazhdan group every continuous equivariant injection of a Bernoulli shift over a transitive set is surjective
refuted_by:
  - compressed-coset-shifts-carry-strict-equivariant-embeddings
---

**REFUTED.** Statement: for every infinite simple group `G` with property (T),
every transitive left `G`-set `X` and every finite alphabet `A`, every
continuous `G`-equivariant injection `A^X -> A^X` is surjective.

This is the architecture "property (T) and simplicity rigidify Bernoulli
dynamics, and rigid Bernoulli dynamics admit no strict self-embeddings". Taking
`X = G` would give `fg-simple-kazhdan-groups-are-surjunctive`.

## Attempts

- *Spectral gap, strong ergodicity, Glasner--Weiss closedness, no finite
  quotients.* All hold for the coset shift `A^(G/V_1)` over `R^x`, and all are
  invariant under the measure conjugacy a strict embedding induces.
- *Refuted* by `compressed-coset-shifts-carry-strict-equivariant-embeddings`:
  the pullback along the compressor surjection `gV_1 -> g u^-1 V_1` is a strict
  continuous equivariant injection of `A^(G/V_1)`.
