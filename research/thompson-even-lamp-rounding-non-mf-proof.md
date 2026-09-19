---
rg: 2
id: thompson-even-lamp-rounding-non-mf-proof
kind: route
title: Upgrade the Thompson finite-state detector to an MF obstruction
target: finite-memory-self-hash-non-mf
requires:
  - thompson-even-lamp-fp-finite-state-detector
  - operator-norm-finite-state-rounding
artifacts:
  - research/artifacts/finite-memory-self-hashing-non-mf-2026-08-23.md
---

Apply operator-norm finite-state rounding to one sufficiently accurate
coordinate of a hypothetical nontrivial norm-corona representation.  The
rounded model has a finite exact joint-character support carrying the Thompson
actor action.  The exact detector makes both the even-lamp and actor images
trivial, contradicting separation of any surviving output word.
