---
rg: 2
id: leavitt-center-is-coefficient-field-citation
kind: route
title: Import the center theorem for prime Leavitt path algebras
target: leavitt-center-is-coefficient-field
requires: []
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

Citation import.  M. G. Corrales García, D. Martín Barquero, C. Martín
González, M. Siles Molina, J. F. Solanilla Hernández, *Centers of path
algebras, Cohn and Leavitt path algebras*, arXiv:1209.4375, center theorem for
prime Leavitt path algebras, instantiated at the one-vertex two-loop graph.

**Trust surface.**  One arXiv preprint (later published in Bull. Braz. Math.
Soc.), not read in the original during this ingestion and not re-derived here
— it is quoted through the source document audited in
`research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md`.  The
instantiation was checked to the extent that the hypotheses are visibly met:
the rose with two loops is a finite graph satisfying Condition (L), and
`L_k(1,2)` is simple, hence prime.

This is a **LITERATURE_INPUT** premise, and it is the *only* external input in
the primality chain other than `connell-group-ring-primality`.  Everything
else — no finite quotients, the unit-span theorem, strong two-sided division —
is formalized in this repository.

**How to remove it.**  Formalize a monomial **basis** for `L_k(1,2)`
(`LeavittNormalForm.lean` already has the spanning half) and compute the
center by comparing coefficients.  That would make the whole chain down to
`leavitt-evaluation-does-not-split-as-module-map` internal except for
Connell's criterion, whose own hypothesis would then be unconditional here.
