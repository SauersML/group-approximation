---
rg: 2
id: mihailova-free-product-detection-no-go-proof
kind: route
title: Apply residual finite-dimensionality of the full free-group C-star algebra
target: mihailova-free-product-actor-erases-q-detection
requires: []
---

Choi's theorem says that the full group C-star algebra `C*(F_n)` is
residually finite-dimensional.  Let `Sigma` be the direct sum of a separating
family of finite-dimensional representations.  It is faithful.  A faithful
representation of a C-star algebra is weakly equivalent to its universal
representation, so every representation of `F_n` is weakly contained in
`Sigma`.

Apply this with `n=2m` to the quasi-regular representation associated to the
displayed free-product action on `Q`.  Its cyclic stabilizer coefficient is
therefore a pointwise limit of vector coefficients of finite-dimensional
exact representations, independently of `Q`.  On the other hand there are
no relators in `F_(2m)`, so arbitrary generator matrices give exact
levelwise actor representations.  This proves both sides of the stated
tradeoff.

For comparison, the direct-product coefficient criterion used in
`mihailova-actor-liftable-ce-proof` is the classical left--right criterion:
finite-dimensional weak containment there is equivalent to hyperlinearity
of `Q`.  The difference between the two actors is precisely the family of
cross commutators `(MFP3)`.
