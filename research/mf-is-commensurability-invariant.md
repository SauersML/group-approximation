---
rg: 2
id: mf-is-commensurability-invariant
kind: claim
title: MF is invariant under abstract commensurability
distinct_from:
  corona-finite-index-radical-heredity: That is the exact radical identity across a finite-index inclusion; this is the weaker truth-value consequence, kept separate because it is the statement the literature already records and the one the no-virtual-repair arguments cite.
  mf-not-closed-under-integer-extensions: That is a failure statement for infinite-index (cyclic) extensions; this is a permanence statement for finite index, and the two together delimit exactly which extensions preserve MF.
artifacts:
  - GroupApproximation/Sofic/InducedCoronaMF.lean
---

For a finite-index inclusion `H <= G`, the group `H` is MF if and only if `G`
is.  Hence abstractly commensurable groups are simultaneously MF or
simultaneously not, and "virtually MF" is the same condition as MF.

The same finite-index induction gives the parallel permanence statements for
residual finiteness, linearity over a fixed field, and maximal almost
periodicity.
