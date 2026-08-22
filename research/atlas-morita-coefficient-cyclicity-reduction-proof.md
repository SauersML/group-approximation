---
rg: 2
id: atlas-morita-coefficient-cyclicity-reduction-proof
kind: route
title: Saturate by matrix units and read the conjugate chart blockwise
target: atlas-morita-coefficient-cyclicity-reduction
requires: []
---

For `E=k^q tensor k^m`, saturation by the first full matrix algebra sends a
subspace `D` to `k^q tensor U_D`, where `U_D` is the span of all multiplicity
coordinates occurring in `D`.  This proves `(MCC3)` and `(MCC6)`.

If `T=(T_ia)` and `T^(-1)=(S_bj)`, direct block multiplication gives

```text
[T(E_ab tensor 1)T^(-1)]_(ij)=T_ia S_bj.
```

Every first-chart invariant subspace is uniquely `k^q tensor U`.  It is
invariant under the conjugate chart exactly when `U` is invariant under all
the displayed blocks, hence under `C_T`.  Intersecting all common invariant
subspaces containing `D` proves `(MCC4)` and `(MCC5)`.

Finally each chart saturation multiplies dimension by at most `q^2` by the
coordinate-span calculation, including after conjugating coordinates by
`T`.  Iteration gives `(MCC7)--(MCC8)`, and rank subadditivity over the
thirteen residual images gives `(MCC9)`.
