---
rg: 2
id: explicit-exact-support-lcs-witness
kind: claim
title: Freeze one explicit LCS submenu certified by the exact-support mass gap
artifacts:
  - research/artifacts/lcs-exact-support-sparsification-2026-08-18.md
---

From a proved instance of `bcs-to-lcs-exact-support-gap`, produce an explicitly
listed finite linear system `Ax=b` (equivalently its full solution-group
presentation), its central involution `J`, and rational/checkable constants
certifying both sides of the sparsification argument:

1. an exact tracial representation satisfying every selected LCS relation and
   sending `J` a fixed positive normalized-2 distance from `1`; and
2. one positive relator tolerance below which no finite-dimensional approximate
   representation of the listed solution group keeps `J` separated by the
   chosen constant.

The probabilistic inequality in `exact-support-relator-sparsification` proves
that some finite submenu works.  This node enforces Cairn's stronger root word
**explicit**: the actual equations, not merely their existence, must be frozen
in the repository.

## Attempts

- Once the exact-support/soundness proof is effective, enumerate the finite
  support of the LCS check distribution and use conditional expectation to
  choose checks one at a time while maintaining the strict profile-net margin.
- Prefer a proof of soundness which supplies finitely many rational orbit
  inequalities; then each candidate submenu has a machine-checkable symbolic
  certificate rather than relying on numerical sampling over matrix sizes.
- If the BCS source is generated effectively from a fixed nonhalting-machine
  instance of the MIP*=RE construction, keep the entire compiler deterministic
  so the final word list is explicit even if enormous.
