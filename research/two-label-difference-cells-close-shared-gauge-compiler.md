---
rg: 2
id: two-label-difference-cells-close-shared-gauge-compiler
kind: route
title: Cancel the two adjacent swaps with authenticated label-difference cells
target: binary-leavitt-two-shared-gauge-selector-compiler
requires:
  - same-center-whitehead-analytic-candidate-package
  - binary-leavitt-two-label-difference-occurrence-cells
  - center-chain-four-hecke-flags-have-native-ranks
---

On the positive subcorner supplied by the new occurrence cells, substitute
the Whitehead normal forms `(LDC1)` into `(LDC2)`.  The label-only formulas
`(LDC3)` cancel the adjacent swaps and give `(LDC5)`.  The ordinary
Whitehead braid already makes `V_1,V_2` unitarily conjugate, so their
positive spectral fractions agree.

The authenticated native source rows retain fractions `1/2,1/4`, while the
two label-only target factors in `(LDC5)` have fractions `1/4,1/8`.
`center-chain-four-hecke-flags-have-native-ranks` verifies these four fixed
packet ranks independently of any occurrence identification.  The positive
mass bound `(LDC4)` and the relation-controlled boundary estimates therefore
give exactly `(SGS1)--(SGS2)` of
`binary-leavitt-two-shared-gauge-selector-compiler`.

No use is made of the equalized full-`Q` source normalization.  In
particular, `b2-b3-pair-full-hecke-four-native-sectors` supplies a useful
common quarter source but cannot replace the two original native source
rows: `full-hecke-quarter-source-equalizes-selector-ranks` shows that doing
so changes their fractions to `1/2,1/2` and removes the affine obstruction.
