---
rg: 2
id: amplification-natural-multiplicity-no-go-proof
kind: route
title: Tensor every authenticated tape letter with the spectator identity
target: amplification-natural-words-cannot-read-packet-multiplicity
requires:
  - two-generator-amitsur-levitzki-dimension-oracle
  - packet-natural-selectors-cannot-extract-one-bounded-copy
  - fixed-packet-hall-atlas-has-no-julia-cutoff-gap
---

Word evaluation, compression by a fixed packet idempotent, and fixed block
matrix operations all commute with `U -> U tensor I_l`, proving `(ANW2)`.
Polynomial identities are unchanged by tensoring a represented algebra with
the identity, whereas Schur multiplicity is multiplied by `l`.  This proves
the claimed separation between PI degree and raw multiplicity.
