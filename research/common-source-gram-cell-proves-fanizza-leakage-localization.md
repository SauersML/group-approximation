---
rg: 2
id: common-source-gram-cell-proves-fanizza-leakage-localization
kind: route
title: Convert the common capacity-gated source Gram cell into NCL13
target: shared-fanizza-exit-leakage-localization
requires:
  - capacity-gated-common-corner-bcs-two-cell
  - capacity-gated-common-source-gram-word-cell
---

Apply `(CGC4)` to the common source projection `(CSG1)` for each exit and sum
the fixed finite family.  The word-cell estimate `(CSG3)` yields `(CSG4)`,
which is precisely the localized functional bound `(SFEL2)`.  Fixed packet
rounding and word telescoping contribute only the displayed `o(1)` term.

The construction remains compatible with exact marked completeness for the
reasons in the two input nodes.  No near-full overlap, polar gauge, or
universal tracial corner compression is used.
