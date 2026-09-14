---
rg: 2
id: low-degree-strict-pairs-have-one-sided-linear-parts-proof
kind: route
title: Substitute the encoder into the reduced decoder and read degree one below the reduction threshold
target: low-degree-strict-pairs-have-one-sided-linear-parts
requires: []
artifacts:
  - research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md
---

Direct proof, Sections 1 and 2 of the artifact.

1. Normalize by translation, so `tau(0) = 0 = sigma(0)`.
2. Substitute the encoder's reduced component polynomials, which have zero constant term,
   into the decoder's reduced local rule.
   - A decoder monomial of total degree `D` becomes a product of `D` polynomials without
     constant term. Every resulting monomial has total degree at least `D`, and every
     exponent is at most `D deg tau < q`.
   - Product coincidences in `G` merge variables but keep every exponent at most the total
     degree.
3. So the composite polynomial is reduced, and its degree-one part is the linear part of
   `tau_C tau_A = tau_(CA)`. The composite is the identity, and reduced representations are
   unique, so `CA = I_m`.
4. The dichotomy follows. If `AC != I`, `tau_A` has left inverse `tau_C` and is not onto. If
   `AC = I`, `tau_C` is bijective and linear, and `tau_C tau` has identity linear part.
