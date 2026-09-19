---
rg: 2
id: affine-active-leavitt-envelope-proof
kind: route
title: Split the infinite active carrier and compare finite module dimensions
target: affine-active-corner-has-faithful-binary-leavitt-envelope
requires:
  - affine-s3-active-idempotent-toeplitz-envelope
  - kleene-completeness-needs-only-a-nontrivial-exact-representation
---

The countable faithful-module construction in the claim gives a
representation of the presented algebra whose restriction to `S` is
faithful; therefore the canonical coefficient map is injective.  The
presentation is finite because `S` is finite-dimensional over a finite field
and `(ALE1)` adds four generators and finitely many relations.

The column `(s_0,s_1)^T` and row `(t_0,t_1)` are mutually inverse module
maps between `AL_A(S)` and two copies of that module, proving `(ALE2)`.
Applying the same maps to a finite-dimensional module gives `(ALE3)`.  In a
stably finite target the same rectangular equivalence makes the idempotent
`A` properly infinite; stable finiteness forbids that unless `A=0`.
