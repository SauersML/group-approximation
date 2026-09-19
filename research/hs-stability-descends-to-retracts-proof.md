---
rg: 2
id: hs-stability-descends-to-retracts-proof
kind: route
title: Pull an approximate representation across the retraction and restrict its correction
target: hs-stability-descends-to-retracts
requires:
  - infinite-hyperlinear-kazhdan-group-is-not-hs-stable
---

Given an asymptotic same-dimensional representation `phi_n` of `H`, compose
with `r` to obtain `phi_n r` on `L`.  Stability of `L` gives exact
same-dimensional representations `pi_n` of `L` close to `phi_n r` on every
fixed element.  Then `pi_n i` is an exact representation of `H`, and by
`r i=id_H` it is close to `phi_n`.  This proves descent.

For the consequence, descent would make the infinite hyperlinear
property-(T) retract `H` HS-stable, contradicting
`infinite-hyperlinear-kazhdan-group-is-not-hs-stable`.

