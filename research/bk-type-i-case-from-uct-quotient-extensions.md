---
rg: 2
id: bk-type-i-case-from-uct-quotient-extensions
kind: route
title: The UCT-quotient extension case glues each CCR subquotient of a stably finite type I algebra onto its quasidiagonal ideal
target: bk-type-i-stably-finite-algebras-are-qd
requires:
  - blackadar-kirchberg-for-uct-quotient-extensions
  - separable-ccr-algebras-are-quasidiagonal
artifacts:
  - research/artifacts/bk-type-i-k0-embedding-equivalence-2026-09-16.md
---

Artifact §7.1.  This is the induction of route `bk-type-i-case-via-k0-embedding`,
with the successor step supplied directly by the extension claim.

Let `E` be separable, stably finite and type I, with a countable composition
series `(I_α)_{α ≤ β}` whose subquotients are CCR.  Induct on `α`.

- **Limits.**  The closure of an increasing union of QD ideals is QD.
- **Successor `α + 1`.**  Consider `0 → I_α → I_{α+1} → B → 0`.
  - `I_α` is separable, QD by induction, and nuclear, since type I algebras are
    nuclear.
  - `B = I_{α+1}/I_α` is separable and CCR, hence QD by
    `separable-ccr-algebras-are-quasidiagonal`.  It is nuclear, and UCT
    (Rosenberg--Schochet; not re-checked).
  - `I_{α+1}` is a C\*-subalgebra of the stably finite `E`, so it is stably
    finite.
  - `blackadar-kirchberg-for-uct-quotient-extensions` makes `I_{α+1}` QD.

So `E = I_β` is QD.
