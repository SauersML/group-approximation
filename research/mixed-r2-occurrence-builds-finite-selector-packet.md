---
rg: 2
id: mixed-r2-occurrence-builds-finite-selector-packet
kind: route
title: Use the cross-chart R2 triangle to identify the two fixed S6 charts
target: bleak-quick-adjacent-seam-retains-finite-selector-packet
requires:
  - bleak-quick-adjacent-seam-retains-one-mixed-r2-cell
  - mixed-r2-cell-couples-shared-s5-extension-multiplicities
---

Apply `(MRC4)` to `(BMR2)` and the private chart-one R2 triangle.  After the
`O(delta)` errors in `(BMR1)` are included, it gives `(BMR3)`.

Use `Phi_0` as the map `Phi` required by the target selector-packet claim.
Its complement selectors

```text
Phi_0((j k)),       Phi_0((k l)),       Phi_0((l q))
```

commute with `X_0=Phi_0((i p))+O(delta)` up to `O(delta)`.  Equation `(BMR3)`
then gives the same three commutator bounds for `X_1`.  The common-pivot arm
and both contextual Carmichael products are already part of the two local
six-letter charts in `(BMR1)`.  Thus all clauses of `(BSP1)` hold with a
larger universal constant.

This route does not infer a joint S6 extension merely from a common S5 face.
The mixed R2 cell first removes the multiplicity rotation; only then is one
private chart used as the common packet.

