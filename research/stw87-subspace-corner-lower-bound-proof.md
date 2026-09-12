---
rg: 2
id: stw87-subspace-corner-lower-bound-proof
kind: route
title: Compression identifies a subspace uniform Roe algebra with a hereditary corner
target: stw87-subspace-corner-lower-bound
requires:
  - stw87-wz-upper-bound
---

Put `p_Y=χ_Y` in the diagonal `ℓ^∞(X) ⊆ C*_u(X)`.  Compression of a
finite-propagation operator on `ℓ²(X)` has the same propagation bound on
`ℓ²(Y)`.  Conversely, zero extension from `ℓ²(Y)` to `ℓ²(X)` preserves
propagation.  Taking norm closures therefore identifies
`p_Y C*_u(X) p_Y` with `C*_u(Y)`.  This is a hereditary subalgebra, so
Winter--Zacharias, Proposition 2.5, gives the dimension inequality.  For the
last assertion, combine it with the upper bound and `asdim(X)=n`.
