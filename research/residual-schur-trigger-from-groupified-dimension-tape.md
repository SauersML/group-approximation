---
rg: 2
id: residual-schur-trigger-from-groupified-dimension-tape
kind: route
title: Run the endogenous polynomial-identity stop in the residual commutant
target: residual-commutant-supercritical-schur-trigger
requires:
  - schur-residual-commutant-is-a-dimension-oracle-tape
  - constant-hs-groupification-of-residual-dimension-tape
---

The exact tape theorem identifies the current residual factor and guarantees
that its finite dimension triggers a failed instruction.  The groupification
claim transports that endogenous failure with constant normalized-HS cost and
activates `r>log_2L` independent Schur cells in the same factor.  Its escape
branches pay the fixed energy floor, exactly giving `(RST1)`.

