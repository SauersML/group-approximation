---
rg: 2
id: uniform-area-bounds-essential-chart-count
kind: claim
title: Uniform filling area bounds the number of essential chart instances
invalidates:
  - growing-chart-count-closes-tagged-code
artifacts:
  - research/uniform-area-essential-chart-count-proof.md
distinct_from:
  bounded-tagged-mark-seam-complex-has-finite-row-range: that assumes a bounded chart complex with pairwise mark seams and proves finite output range; this proves the bounded-chart hypothesis is automatic for every positive-area chart decomposition of a uniformly bounded filling.
  fixed-arity-mark-fusion-has-finite-character-model: that permits a genuine non-pairwise cell but fixes its arity; this rules out increasing the number of independent positive-area chart cells while retaining a uniform total filling bound.
---

**ESTABLISHED DIAGRAM-COUNT FIREWALL.**  Fix a finite presentation and let
`D` be a van Kampen diagram with

```text
Area(D)<=B.                                             (UAC1)
```

Suppose `D` is decomposed into chart instances with disjoint two-cell
interiors, where an **essential** chart contains at least one presentation
two-cell.  Then

```text
number of essential charts <= Area(D) <= B.            (UAC2)
```

If proposed chart labels overlap on the same two-cells, `(UAC2)` applies to
every cell-disjoint subfamily.  Reusing one cell under arbitrarily many chart
labels does not create arbitrarily many independent relator applications;
it is a different direct-diagram proposal, not a decomposition into growing
positive-area chart instances.  A chart with no two-cell is only a labelled
graph.  It may contain a long conjugating path, but it contributes no
presentation relator and hence no independent fusion equation.

Therefore a uniformly bounded-area family cannot evade a bounded-chart
seam theorem by letting the number of **cell-disjoint relator-bearing** chart
instances grow with the address.  What may grow is a cell-free conjugating
graph, overlapping chart labels, or the boundary length of one chart.  None
adds a relator application; any use of those structures must be controlled
by a separate direct-diagram argument.

Applied to `(CCC2)`, a growing-chart proposal has at most the uniform edge
area many essential charts.  Thus the surviving chromatic possibilities are
a fixed number of genuinely non-pairwise payload-fusion cells, or a direct
bounded-area diagram whose load-bearing cells cannot be isolated as mark
charts—not an unbounded collection of positive-area local charts.  No
Property `(T)`, Kazhdan input, matrix approximation, or literature theorem
is used.

DERIVATION
uniform-area-essential-chart-count-proof
