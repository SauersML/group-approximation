---
rg: 2
id: stw01-sigma-unital-cuts-have-quasitracial-idempotence
kind: claim
title: One functional-calculus approximate unit is asymptotically idempotent for every bounded quasitrace
distinct_from:
  stw01-asymptotic-quasitracial-cuts-promote-linearity: that theorem promotes a quasitrace once suitable cuts are given; this result constructs the idempotent cuts and, in a separable ambient algebra, makes them norm-quasicentral
  stw01-qt-idempotent-approximate-units-preserve-linearity: that theorem requires exact membership of every finite-stage defect in a universal square-null radical; here the defects generally remain nonzero and only converge to zero under each bounded quasitrace
artifacts:
  - research/artifacts/stw01-sigma-unital-extension-audit-2026-08-30.md
---

Let `I triangleleft A` be a sigma-unital ideal in a unital C*-algebra.  There
is an increasing positive-contractive approximate unit `(e_n)` for `I` such
that, simultaneously for every bounded `2`-quasitrace `tau` on `A`,

```text
tau((e_n-e_n^2)^2) -> 0.                                  (SFC1)
```

The sequence may be chosen inside `C*(h)` for one strictly positive
contraction `h in I` (with the zero ideal understood trivially).

If `A` is separable, the same sequence can moreover be chosen
norm-quasicentral in `A`.  Thus in the separable-ambient case it also
satisfies

```text
tau([e_n,a]*[e_n,a]) -> 0             (a in A)             (SFC2)
```

for every bounded `2`-quasitrace `tau` on `A`.

Ambient separability cannot be replaced here by separability of `I` alone;
see `stw01-separable-ideal-does-not-force-sequential-qcau`.
