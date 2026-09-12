---
rg: 2
id: support-return-atomic-return-fence-proof
kind: route
title: Apply the finite marked chart-groupoid witness to both operator-norm return endpoints
target: support-return-odd-loops-do-not-imply-atomic-return
requires:
  - support-return-gives-gauged-native-loop
  - support-return-charts-meet-in-two-pauli-pairs
  - support-return-selector-occurrence-fence
  - atomic-leavitt-gap-on-nonzero-matrix-corner
  - rank-deficient-return-row-has-operator-norm-one
---

The finite chart-groupoid witness in `(SRL8)` realizes each transported
Pauli chart and its inner quarter-swap action.  The independent central
sign twists from `(SCI6)` extend it while preserving both odd identities and
the native braid.  Take the Pauli simple on which the common extraspecial
center acts by `-I`.  This is a finite-dimensional exact model of `T_SRL`
whose prescribed rounded marked projection is nonzero (indeed the identity).

An implication from `T_SRL` to either proposed return output must apply to
this one exact model at every positive input tolerance.  For Atomic Morita
Return, `(ALG1)` bounds the sum of the three output defects below by one,
whereas the proposed modulus bounds it above by `3 eta(t)->0`.  For the
coarse/fine output, `(ROW7)` makes the leakage norm exactly one, whereas the
proposed modulus makes it at most `omega(t)->0`.  Both conclusions are
impossible.

The witness retains all authenticated support-return relations, not merely
the formal equality `(SRA1)`.  What it omits is precisely any new relation
identifying coefficient completeness with the marked atom.  Therefore the
argument fences only deductions from the stated support-return occurrence
table and leaves the full-presentation decoder targets open.
