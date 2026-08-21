---
rg: 2
id: reverse-kleene-operator-norm-nonmf-proof
kind: route
title: Contrast the collapse threshold with local MF separation
target: reverse-kleene-operator-norm-collapse-gives-non-mf
requires: []
---

Run the same self-referential van Kampen enumerator.  Its fixed instance
cannot halt, so its compiled word is nontrivial and the nonhalting
operator-norm collapse applies.  If the group were MF, local MF separation
would give arbitrarily small relator operator-norm defect while keeping this
nontrivial word at distance at least one from the identity, contradicting
the compiler bound `alpha<1`.

For finitely many marks, tensor powers make each nontrivial corona image have
distance greater than one along a subsequence.  Choose one sufficiently
accurate coordinate for each mark and take their finite direct sum.  Defect
is the maximum of the block defects and every mark is separated on its own
block, contradicting disjunctive collapse.
