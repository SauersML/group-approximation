---
rg: 2
id: leavitt-regular-a5-wreath-map-proof
kind: route
title: Kill the actor by simple nonsoficity and then kill the common commuting A5 image
target: leavitt-regular-a5-wreath-is-minimally-almost-periodic
requires:
  - universal-leavitt-el4-nonsofic
  - binary-leavitt-elementary-group-is-simple
---

Let `rho:(directSum_Q A5) semidirect Q -> U(d)` be exact.  A nontrivial
actor restriction is faithful by simplicity, and its finitely generated
linear image is residually finite by Malcev, hence sofic, contradicting
`universal-leavitt-el4-nonsofic`.  Thus the actor is killed.  Covariance and
transitivity identify all coordinate `A5` images.  Images of two distinct
coordinates commute, so this common image is abelian; perfection of `A5`
kills it.  The actor and one coordinate orbit generate the wreath, proving
minimal almost periodicity.  The embedded actor proves nonsoficity, and the
same finite generating sets prove finite generation.
