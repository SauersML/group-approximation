---
rg: 2
id: two-external-return-s3-proof
kind: route
title: Compute the L0 triangle and extend the three-reflection model by a commuting return
target: two-external-return-cell-has-finite-s3-model
requires:
  - native-weyl-return-gauges-have-s3-model
  - signed-hecke-normalizer-has-eight-external-root-returns
---

For matrix roots `x_ab(1)=I+E_ab`, the standard Steinberg relations give

```text
[x_45(1),x_59(1)]=x_49(1),
[x_78(1),x_59(1)]=1.                                  (1)
```

The exact enumeration identifies `x_59(1)` with the external arrow `9->5`
and puts `x_45(1),x_49(1)` in `L_0`.  On the one-character isotypic
projection the last two therefore have identity reservoir factor.  Writing
the two external restrictions as `N_n tensor E` and `N_r tensor G`, the
reservoir equations in `(1)` are `[1,G]=1` and `[E,G]=1`.

Take the three reflections from the preceding native-Weyl model and put
`G=E=(2 3)`.  Conjugating `(2 3)` by `(1 2)` gives `(1 3)`, and conjugating
`(1 3)` by `(2 3)` gives `(1 2)`, so every old factorization row remains
exact.  The new commutation holds because `G=E`; the scalar triangle is
automatic.  The product `DE=(1 2)(2 3)` is still a nonidentity three-cycle.
Assigning every transported occurrence its literal conjugate verifies all
additional naturality squares and completes the finite model.

