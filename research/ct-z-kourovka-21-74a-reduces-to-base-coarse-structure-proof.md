---
rg: 2
id: ct-z-kourovka-21-74a-reduces-to-base-coarse-structure-proof
kind: route
title: "Run the neutral-prime proof over an abstract splitting of the base: a Haar-measure argument gives every indecomposable component a nontrivial holonomy, which bounds or radializes the fibre; Conway's map is one mixing component with a translation holonomy"
target: ct-z-kourovka-21-74a-reduces-to-base-coarse-structure
requires:
  - ct-p-z-neutral-primes-kourovka-21-74a-is-decidable
  - ct-z-residue-partition-certificates-live-on-s-adic-coordinates
  - conway-amusical-permutation-is-the-full-three-shift
---

Lane proof (bh-2174-rank2, 2026-09-19), not reviewed. The argument is in the body of
`ct-z-kourovka-21-74a-reduces-to-base-coarse-structure`. It uses:
- the neutral-prime node's degeneracy test, D1–D3 bounds and radial truncation (Lemmas 1–3);
- Theorem 1 (skew product) of the S-adic node;
- item 2 (conjugacy to the full 3-shift) of the Conway node, for the Corollary.

New ingredients: the Haar-measure argument that an indecomposable, infinite-order component always
carries a nontrivial holonomy, and the translation bound.
