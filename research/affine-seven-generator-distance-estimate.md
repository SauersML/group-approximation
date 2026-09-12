---
rg: 2
id: affine-seven-generator-distance-estimate
kind: claim
title: Seven explicit affine generators control distance to invariant vectors with constant 2 plus 5 sqrt 3000
distinct_from:
  literal-base-explicit-kazhdan-pair: that packages an eight-word pair for an abstract presentation; this proves a distance inequality for seven concrete affine matrices directly from a fixed rational factor and supplies its C-star spectral projection.
artifacts:
  - research/artifacts/affine-seven-generator-distance-estimate-2026-09-08.md
---

Let `B=Z^3 semidirect SL_3(Z)` and let `S` consist of its six elementary
matrix generators and the translation by `e_1`. In every unitary
representation `pi` on any Hilbert space,

```text
dist(x, Fix(pi(B))) <= (2+5 sqrt(3000)) max_(s in S) ||pi(s)x-x||.
```

Consequently the seven-generator Laplacian has spectrum contained in
`{0} union [(2+5 sqrt(3000))^(-2),28]`. Its zero spectral projection
belongs to the represented unital C-star algebra, and the same statement
holds for homomorphisms into the unitary group of any unital C-star algebra.

The claim asserts this explicit inequality. Its proof derives it from finite
rational arithmetic and the two-primitive-vector decomposition of integer
translations.
