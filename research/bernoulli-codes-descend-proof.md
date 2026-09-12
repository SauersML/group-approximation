---
rg: 2
id: bernoulli-codes-descend-proof
kind: route
title: Split the coordinates into left cosets of the window subgroup and apply Fubini
target: bernoulli-codes-descend-to-window-subgroup
requires: []
artifacts:
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
---

Section 7.2 of the artifact.

1. **Coset-wise action.** `((gk)^-1.x)(k') = x(gkk')`, so `tau(x)(gk)` reads `x` on `gK` only. Put
   `z(k) = x(gk)`. Then `((gk)^-1.x)(k') = (k^-1.z)(k')`, so `tau(x)(gk) = tau_K(z)(k)`.
2. **If `tau` is injective on a conull `S`.** Fix a coset `gK`. By Fubini, for almost every choice of
   `x` off `gK`, the section of `S` is conull in `A^(gK) = A^K`. On it, `tau` restricted to that
   coordinate block is `tau_K`, so `tau_K` is injective on a conull set.
3. **If `tau_K` is injective on a conull `S_K`.** The set of `x` whose block on every coset lies in
   `S_K` is a countable intersection of conull sets. On it `tau` is injective, coset by coset.
