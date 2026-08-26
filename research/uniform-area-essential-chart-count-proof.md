---
rg: 2
id: uniform-area-essential-chart-count-proof
kind: route
title: Charge one presentation two-cell to every essential chart
target: uniform-area-bounds-essential-chart-count
requires: []
---

The area of a van Kampen diagram is its number of presentation two-cells.
Choose one two-cell in every essential chart.  Disjoint interiors make these
chosen cells distinct, which proves `(UAC2)`.

For overlapping chart labels, choose any cell-disjoint subfamily and apply
the same injection into the set of two-cells.  If many labels reuse one
cell, they are not independent positive-area subdiagrams.  A zero-cell chart
is a labelled graph and can carry long boundary or conjugating paths, but it
contains no application of a presentation relator and hence no independent
mark-fusion constraint.  This proves exactly the scoped assertion about
cell-disjoint essential chart count.
