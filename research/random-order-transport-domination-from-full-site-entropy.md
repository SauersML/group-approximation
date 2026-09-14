---
rg: 2
id: random-order-transport-domination-from-full-site-entropy
kind: route
title: Full single-site entropy gives domination of the random-order transport sum
target: injective-ca-random-order-transport-is-dominated
requires:
  - injective-ca-random-order-transport-identity
  - injective-ca-images-have-full-single-site-entropy
artifacts:
  - research/artifacts/random-order-decoder-transport-2026-09-12.md
---
If `H(kappa(x)(e)) >= log |A|`, then the output-side sum, which equals `log |A|` by the identity, is at most
`H(kappa(x)(e))` (artifact Corollary 2).

This route and `full-site-entropy-via-random-order-transport-domination` form an intended cycle recording an
equivalence. Neither establishes either claim.
