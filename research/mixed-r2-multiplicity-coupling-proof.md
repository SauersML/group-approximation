---
rg: 2
id: mixed-r2-multiplicity-coupling-proof
kind: route
title: Cancel the transported arm in one cross-extension R2 triangle
target: mixed-r2-cell-couples-shared-s5-extension-multiplicities
requires: []
---

In `Sym(Omega)`, conjugating `(i p)` by `(i q)` gives `(p q)`, so every
representation satisfies `(MRC2)`.  Conjugation by the unitary `Y_1`
preserves normalized Hilbert--Schmidt norm.  Therefore

```text
||Y_1^* X_0 Y_1-R||_2
 =||X_0-Y_1 R Y_1^*||_2
 =||X_0-X_1||_2,
```

where the last equality is the chart-one identity
`Y_1^* X_1 Y_1=R`.  This proves `(MRC3)`.  If that identity has defect,
insert `Y_1^* X_1 Y_1` between `Y_1^* X_0 Y_1` and `R` and use the triangle inequality,
which proves `(MRC4)`.

For the multiplicity rotation, `U` commutes with `rho_0(H)`, hence with
`R`.  The chart-one triangle still holds exactly.  Substitution into
`(MRC3)` gives `(MRC5)`.  The explicit rotation in
`shared-s5-selector-face-has-multiplicity-rotation-gauge` changes
`rho_0(x)`, so its mixed R2 defect is strictly positive.

Finally map the three letters `(1,01,00)` in the displayed Bleak--Quick R2
cell to `(010,000,001)`.  Its three swaps become respectively `s,t,r`,
which is `(MRC6)`.  This verifies that no new finite-group identity has been
invented; only the cross-occurrence retention remains open.
