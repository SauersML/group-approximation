---
rg: 2
id: finite-type-selector-authenticates-fanizza-row
kind: route
title: Select the Fanizza oriented row by an arbitrary finite multiplicity-coordinate rule
target: fanizza-matrix-coordinate-source-full-compression
requires:
  - finite-graph-of-groups-representation-types-are-integer-flows
  - fanizza-full-reflection-row-has-sharp-mirror-floor
---

**INVALIDATED SELECTOR-ONLY PROPOSAL.**  After exactifying a fixed finite
packet/reset atlas, inspect its finite integer multiplicity vector and use an
arbitrary matrix-coordinate rule--including congruences, divisibility,
lexicographic first-hit choices, Hall matchings, or a direct dimension
oracle--to choose one positive-density reducing packet block.  On that block
declare the corresponding fixed cuts `H<=E`, `F=E-H` to be the selected
oriented row, and attempt to infer

```text
R_F U R_E U^*=1+o_2(1)
```

from the existing chord--reset relations.

`multiplicity-only-fanizza-row-selection-leaves-a-mirror` invalidates this
route.  The selector may be completely nonfunctorial and need not extend to
a finite von Neumann algebra.  Nevertheless it only announces a reducing
block; because the current relations do not couple the chord to its scalar
multiplicity coordinate, one can install the balanced mirror *after* the
selection on exactly that block.  A surviving finite-coordinate mechanism
must impose a new row-sensitive incidence on the selected multiplicity
space, not merely choose the space more cleverly.
