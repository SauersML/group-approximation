---
rg: 2
id: phase-tagged-row-reduction-proof
kind: route
title: Compress the transported projection to the target type and use phase covariance
target: phase-tagged-row-defect-reduces-to-within-type-selector-mismatch
requires:
  - phase-covariance-words-exactly-measure-type-transport-leakage
---

For arbitrary projections `R,Q`, write `R` in blocks relative to
`Q+(1-Q)`.  The relation `R^2=R` gives

```text
||R-QRQ||_2^2<=2 tau((1-Q)R).                           (PTR6)
```

Apply this with `R=UeU^*` and `Q=Q_t`.  Since

```text
tau((1-Q_t)R)=||(1-Q_t)Ue||_2^2=L,
```

the triangle inequality gives

```text
||R-f||_2<=sqrt(2L)+sqrt(I).
```

Squaring with `(a+b)^2<=2a^2+2b^2` proves `(PTR2)`.  Since `e<=Q_s`,
`L<=||(1-Q_t)UQ_s||_2^2`; sum the rows and apply `(PTR3)` to obtain
`(PTR4)`.

