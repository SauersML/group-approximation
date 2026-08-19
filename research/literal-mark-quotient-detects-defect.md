---
rg: 2
id: literal-mark-quotient-detects-defect
kind: route
title: Detect the unsquared defect through the literal marked quotient
target: unsquared-defect-mf-visible
requires: [literal-mark-quotient-mf, commuting-lamp-defect-survives]
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Why sufficient

`commuting-lamp-defect-survives` gives a nontrivial image of `u` in
`W/<zeta>`, and `W/<zeta>` is a quotient of `E/<w>`; hence `u` is not in
`<w> = {1,w}`.  If `E/<w>` is MF, compose `E -> E/<w>` with a faithful
norm-matrix-corona representation of the quotient: the result is a corona
representation of `E` that does not kill `u`.

This makes `literal-mark-quotient-mf` a second route to
`unsquared-defect-mf-visible` alongside `commuting-lamp-mf-detects-defect`,
so the two open quotient-MF claims are jointly refuted by a single negative
answer to `corona-commutant-no-growth`.
