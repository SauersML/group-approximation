---
rg: 2
id: mf-integer-extension-nonclosure-proof
kind: route
title: Combine the LEF base with the non-MF witness
target: mf-not-closed-under-integer-extensions
requires: [lamp-telescope-base-is-lef, sofic-non-mf-witness, lef-implies-operator-mf, literal-telescope-core-lef, literal-central-mark-corona-invisible]
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Why sufficient

`lamp-telescope-base-is-lef` makes the kernel LEF, hence MF by
`lef-implies-operator-mf`.  The quotient of `W` by that kernel is `Z` by the
manuscript's reassociation of the iterated semidirect product.
`sofic-non-mf-witness` supplies the failure of MF for the middle group.

The second witness runs identically with `literal-telescope-core-lef` in place
of `lamp-telescope-base-is-lef`, `E_T` in place of `ClLamp(X) semidirect T`,
and `literal-central-mark-corona-invisible` in place of
`sofic-non-mf-witness`.
