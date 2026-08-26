---
rg: 2
id: external-8-to-7-one-singer-square-cancels-whitehead-gauge
kind: route
title: Use the external 8-to-7 return and one Singer square to cancel the first Whitehead gauge
target: el20-six-moving-coefficient-square-bridges
requires:
  - signed-hecke-normalizer-has-eight-external-root-returns
---

This route chooses `n=x_78(1)`, the external signed normalizer on the same
coordinate pair as `J_1`, and tries to infer equality of its multiplicity
involution `E_(8,7)` with the Whitehead gauge `D_1` from the single
source-to-target covariance square.

It is invalidated by
`one-singer-square-does-not-identify-external-return-gauge`.  On the source
and target Hecke-character carriers the square says exactly

```text
E'_(8,7)=D_1 E_(8,7) D_1^(-1),
```

which transports the external involution but does not identify it with
`D_1`.  The exact multiplicity model
`D_1=Z tensor I`, `E_(8,7)=I tensor Z` satisfies the square and retains
distance `sqrt(2)` between the two gauges.

The route remains viable only after adjoining another mixed full-EL20
relation forming a closed loop with unequal odd occurrence parity.  That
stronger route is not invalidated here.


