---
rg: 2
id: toeplitz-finite-head-extension-proof
kind: route
title: Use a finite packet head over the algebraic unilateral shift
target: toeplitz-finite-head-extension-preserves-root
requires:
  - schur-idempotent-is-an-injective-toeplitz-defect
  - schur-toeplitz-envelope-has-proper-self-embedding
---

Take infinitely many augmentation simples and one copy of every other packet
simple.  The packet differs from its augmentation by finite-support matrices,
while the forbidden idempotent is a nonzero finite-support projection.  The
unilateral shift with that projection as cokernel realizes the coefficient
relations.  Compression plus the head augmentation descends the self-map.
The symbol sequence has locally finite elementary kernel and residually
finite Laurent elementary image.  Injectivity of the descended self-map
identifies the ascending HNN group with the corresponding direct-limit-by-
cyclic semidirect product.  Its embedded base contains the nonzero root over
the finite head projection, proving the claim.  No sofic permanence assertion
is made for the locally-finite-by-residually-finite base.
