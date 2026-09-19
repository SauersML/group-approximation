---
rg: 2
id: periodic-higman-algebraic-matrix-certificate-proof
kind: route
title: Verify the cyclic matrix identity and select a non-torsion algebraic unit
target: periodic-higman-algebraic-matrix-certificate
requires: []
artifacts:
  - research/artifacts/periodic-higman-cofinite-spectrum-2026-09-04.md
  - experiments/periodic_higman_algebraic_certificate.py
---

Sections 1–2 of the artifact give a direct proof. Monic polynomial division
verifies the determinant, inverse, and commutator identities over
`Z[i,1/2,L]/(P)`. Conjugation by `diag(i,1)` supplies all four equations.
A Vieta and triangle-inequality argument supplies a root `lambda` of
modulus greater than one, hence not a root of unity. The integral inverse
identity makes it a unit. The reduction `P mod (2,i-1)=(L+1)^5` proves
the assertion at primes above two.

The accompanying verifier reproduces every polynomial and matrix identity
using rational arithmetic. No numerical root isolation, irreducibility
assumption, or finite-group enumeration is used.
