---
rg: 2
id: fpbs-mal-stage-bernoulli-shift-free-for-non-dirac-base
kind: claim
title: The Bernoulli shift of a countably infinite group over a non-Dirac base measure is essentially free
---

**OPEN.** Let `Gamma` be a countably infinite group, let `Z` be a standard
Borel space, and let `nu` be a Borel probability measure on `Z` that is not a
point mass. Then the Bernoulli shift `(gamma x)(delta) = x(gamma^{-1} delta)`
on `(Z^Gamma, nu^Gamma)` is essentially free: for every `gamma ≠ 1`,
`nu^Gamma{x : gamma x = x} = 0`. In particular every subgroup of `Gamma` acts
essentially freely.

This is the freeness import used in step 2 of
`fpbs-mal-stage-block-sprinkling-threshold-proof`. For a point mass the space
is a single point and the statement fails.

## Attempts

1. **Constancy on cyclic cosets (2026-09-17, deferred).** `gamma x = x` forces
   `x` to be constant on every coset `<gamma> delta`. If `gamma` has infinite
   order, each such coset is infinite and constancy on it has probability 0.
   If `gamma` has finite order `k > 1`, there are infinitely many disjoint
   cosets of size `k`. The constancy events on them are independent, and each
   has probability `P(z_1 = ... = z_k) < 1` for iid `z_i ~ nu`, because `nu`
   is not a point mass. So their intersection has probability 0. *Deferred:*
   this is standard, and it has not been written as a route or checked by a
   referee. The step to check is `P(z_1 = z_2) < 1` for a diffuse or mixed
   `nu`, which holds because `nu x nu` gives the diagonal mass at most
   `sup_z nu{z} < 1`.
