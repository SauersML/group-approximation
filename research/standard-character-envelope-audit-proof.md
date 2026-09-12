---
rg: 2
id: standard-character-envelope-audit-proof
kind: route
title: Compare trace pullbacks and normal kernels in the three standard envelopes
target: standard-character-envelopes-do-not-supply-signed-bcs-quotient
requires:
  - cdi-character-cannot-be-promoted-by-regular-corners
  - thompson-v-central-extensions-split
  - central-character-rigid-sector-forbids-relator-quotients
---

For CDI, the constructed non-CE factor representation supplies a normalized
character distinct from both the regular and trivial characters.  Therefore
the proposed regular-or-finite-dimensional classification is false for that
chosen group, regardless of property `(T)`.  Tensoring with a scalar finite
central character is an affine injection of this trace simplex into the
marked direct-product sector.

For a wreath product, compose any trace of `C*(H)` with the quotient induced
by `(SCE1)`.  The pullbacks of the trivial and regular traces differ on every
nonidentity element of `H`, so the source is not monotracial.  Cutting a
direct-product finite central factor by a one-dimensional character gives a
corner canonically isomorphic to `C*(W)`, and hence changes nothing.

For Thompson `V`, the established trace simplex contains both the trivial
and regular endpoints, while every central extension splits.  Thus every
one-dimensional central-character cut retains both endpoints.  Simplicity
gives the stated group-kernel dichotomy.  The final analytic-quotient
statement follows from the GNS-kernel calculation in
`central-sector-relator-kernel-proof`.

