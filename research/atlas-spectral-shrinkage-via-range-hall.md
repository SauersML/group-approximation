---
rg: 2
id: atlas-spectral-shrinkage-via-range-hall
kind: route
title: A negative block-range Hall objective supplies the atlas shrunk subspace
target: atlas-spectral-shrunk-intertwiner-certificate
requires:
  - block-range-hall-implies-shrunk-subspace
  - atlas-spectral-range-hall-certificate
---

Take the quadratic form, cutoff and source-block subset `A` supplied by
`atlas-spectral-range-hall-certificate`.  Its `(ARH1)--(ARH2)` are exactly the
small-energy and cutoff-scale requirements `(ASI1)--(ASI2)`.

Apply `block-range-hall-implies-shrunk-subspace` to the low-energy operator
space `K_delta`.  The block-range inequality `(ARH3)` gives

```text
X_delta = direct_sum_(i in A) H_i
```

with

```text
dim(X_delta)-dim(K_delta(X_delta)) >= gamma d.
```

This is `(ASI3)`.  Therefore the range-Hall certificate establishes the full
spectral shrunk-intertwiner certificate, and the existing direct route
`nonhyperlinear-from-atlas-spectral-shrinkage` then closes the primary goal.

The point of this decomposition is algorithmic: one need not solve general
noncommutative rank first.  It is enough to find a mixed atlas Laplacian whose
low-energy **collective block ranges** violate one submodular Hall inequality.
