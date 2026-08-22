---
rg: 2
id: arith-clifford-covariance-skew-tensor-proof
kind: route
title: Conjugate-double the Clifford normalizer labels and skew-tensor the arithmetic enemy
target: arith-clifford-covariance-preserves-projective-energy
requires:
  - finite-projective-sector-groupoids-have-conjugate-absorbers
  - projective-trace-square-transfer-for-sl3-pair
  - spherical-quadrature-tensors-through-clifford-folner-windows
---

# Conjugate-double the Clifford normalizer labels and skew-tensor the arithmetic enemy

Conjugate doubling cancels the finite Mackey cocycle, so the normalizer
labels become an honest representation `T`.  Tensor each arithmetic
generator with its corresponding `T`-matrix, but tensor the relative
commutant witness/block swap with the identity.  Arithmetic relators then
have exactly their old normalized-Hilbert--Schmidt defects, mixed covariance
relations hold exactly, and every relative commutator is its old value
tensored with the identity.  Trace squares are therefore unchanged.

For an arbitrary HNN word the same substitution factors its value into the
old arithmetic/HNN word and a bounded packet matrix determined only by the
arithmetic projection.  Multiplication by the latter cannot destroy a
vanishing normalized trace, so regular-character enemies survive as well.

This proves the claim and upgrades the commuting tensor escape to all
one-path arithmetic--Clifford normalizer covariance incidences.
