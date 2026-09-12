---
rg: 2
id: atlas-literal-augmented-residual-count-proof
kind: route
title: Compare the eliminated two-chart presentation with the maximal-tree filling presentation
target: atlas-literal-augmented-residual-count-is-fourteen
requires:
  - atlas-a4-packet-biclique-decomposition
  - atlas-thirteen-vf-fillings-are-tietze-irredundant
---

`atlas-a4-packet-biclique-decomposition` counts four edges in `K_(2,2)` and
eight in `K_(2,4)`, hence twelve distinct packet pair-cubes.  Equation
`(TIR3)` of `atlas-thirteen-vf-fillings-are-tietze-irredundant` displays the
literal presentation and explicitly retains q14 and collision, giving
`12+1+1=14`.

The same theorem's `(TIR1)--(TIR2)` chooses both q14-bridge edges in the
maximal tree.  Hence q14 belongs to the carrier relations, while the twelve
omitted packet edges become stable-letter fillings and collision is the
thirteenth filling.  This proves `(LRC1)--(LRC2)`.  Rank subadditivity over
the fourteen literal residual images proves `(LRC3)`.
