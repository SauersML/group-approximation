---
rg: 2
id: schur-amplified-parity-compressor-hs-return
kind: claim
title: A coefficient-covariant Schur packet amplifies the parity compressor to positive adjoint density
distinct_from:
  parity-compressor-hs-return: that asks whether the bare two-point parity witness already disappears in matrix ultraproducts; this augments the compressor by a Schur Reynolds module of quadratic adjoint density.
  compressor-covariant-packet-reynolds-return: that is the general non-CE BCS coefficient-covariance program; this uses the fixed two-point parity twist to copy a supplied old-commutant range into the forbidden excess space.
---

Construct the coefficient-covariant packet extension of the Toeplitz parity
compressor described in
`parity-compressor-old-commutant-has-positive-density`.  Prove that its
central involution `J` remains nontrivial, while every homomorphism into a
tracial matrix ultraproduct sends `J` to the identity.

The intended finite-dimensional contradiction is now completely specified.
A positive marked carrier gives forbidden Schur mass `q`; `(ARG1)` and the
coefficient placement give an old low-commutator range of adjoint density
`Omega(q^2)`.  The parity implementer copies that whole range orthogonally
into the compressed low-commutator space by `(PTC2)--(PTC5)`, contradicting
property-`(T)` positive-density commutant no-growth at vanishing defect.

Exact completeness may use a properly infinite packet multiplicity, but the
joint group cell must be injective on the parity base.  No assertion about
the bare group `H_T` follows from this augmented construction.

## Attempts

- Using the bare parity projection leaves only one adjoint direction and is
  exactly the unresolved `parity-compressor-hs-return` problem.
- Tensoring an independent Schur packet produces density but no covariance;
  the decoupled exact model has zero relator defect.  The missing theorem is
  precisely the coefficient placement in
  `parity-compressor-old-commutant-has-positive-density`.
