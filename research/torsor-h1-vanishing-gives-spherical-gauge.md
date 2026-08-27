---
rg: 2
id: torsor-h1-vanishing-gives-spherical-gauge
kind: route
title: Apply quantitative torsor triviality to the short spherical relation defects
target: spherical-short-holonomies-admit-local-gauge
requires:
  - spherical-relation-defect-pairs-small-chord
  - relation-defects-obey-permutation-gauge-law
  - short-edge-gauge-torsor-h1-vanishes
---

## Why sufficient

After the independently chosen tight shadow matchings are completed, charge
the completion roots and the unitary-bad roots to one exceptional set.
`spherical-relation-defect-pairs-small-chord` then says that every relation
holonomy

```text
delta_(g,h,k)=sigma_k^(-1)sigma_g sigma_h
```

moves every remaining cloud point by radius `rho=o(1)` after transporting the
output chord back through the tight `k`-matching.

`relation-defects-obey-permutation-gauge-law` identifies simultaneous source
correction with the affine system `(SGT2)`.  Because the defects come from one
actual table of permutations, their relations among relations satisfy the
exact compatibility identities of the fixed source complex.  Apply
`short-edge-gauge-torsor-h1-vanishes`: it supplies corrections `c_s` of
geometric radius `O_T(rho)` outside `O_T(eta)N` roots and solves all tested
multiplication cells there simultaneously.

Taking the matching tolerance and pointwise defect threshold small enough
makes both quantities below the prescribed `eps`.  This gives all three
clauses of `spherical-short-holonomies-admit-local-gauge` without requiring
Hamming-small corrections or a general stability theorem for permutations.
