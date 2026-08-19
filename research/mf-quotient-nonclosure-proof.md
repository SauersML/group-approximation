---
rg: 2
id: mf-quotient-nonclosure-proof
kind: route
title: Quotient the rank-eight free group onto the literal non-MF group
target: mf-quotient-nonclosure
requires: [literal-group-fails-mf-conventions]
artifacts:
  - non_mf_groups_exist.tex
  - notes/NON_MF_IMPACT_FORMAL_STATUS.md
  - GroupApproximation/Sofic/LiteralMFQuotientControls.lean
  - GroupApproximation/Sofic/FreeGroupResiduallyFinite.lean
---

## Why sufficient

Residual finiteness of `F_8` supplies separating finite-dimensional regular
representations, hence an MF model.  Sending its ordered free generators to
the eight displayed generators of `E` gives the canonical presentation map,
which is surjective.  Its target is not MF by
`literal-group-fails-mf-conventions`.  The three exact clauses are packaged
by `manuscriptQuotientNonclosure`.
