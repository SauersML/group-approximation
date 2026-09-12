---
rg: 2
id: full-site-entropy-via-random-order-transport-domination
kind: route
title: Domination of the random-order transport sum by the site entropy gives full single-site entropy
target: injective-ca-images-have-full-single-site-entropy
requires:
  - injective-ca-random-order-transport-identity
  - injective-ca-random-order-transport-is-dominated
artifacts:
  - research/artifacts/random-order-decoder-transport-2026-09-12.md
---
The identity says the output-side transport sum at `e` equals `log |A|`, and domination says that sum is at most
`H(kappa(x)(e))`. Together they give `H(kappa(x)(e)) >= log |A|` (artifact Corollary 2).

This route and `random-order-transport-domination-from-full-site-entropy` form an intended cycle recording an
equivalence. Neither establishes either claim.
