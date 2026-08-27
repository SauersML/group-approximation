---
rg: 2
id: leavitt-presentation-double-retention-proves-hyperlinear
kind: route
title: Compress the left-right presentation-double model onto the retained sector
target: binary-leavitt-unit-group-hyperlinear
requires:
  - leavitt-positive-rank-intertwiner-retention
  - simple-map-quotient-has-rigid-fd-restriction
  - shulman-double-forces-unstable-kernel-restriction
  - binary-leavitt-elementary-group-is-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
  - hyperlinear-elementwise-visibility
---

Compress `Pi_n(f)` to `W_n`. Write `A_n(f)=P_n Pi_n(f)P_n|W_n`. Condition
`(IR1)` for `f` and `f^(-1)` gives

```text
||1-A_n(f)^*A_n(f)||_(2,r_n) -> 0,
||1-A_n(f)A_n(f)^*||_(2,r_n) -> 0,
```

and the leakage identity gives

```text
||A_n(f)A_n(g)-A_n(fg)||_(2,r_n) -> 0.
```

Replace `A_n(f)` by a polar unitary `sigma_n(f)`; the replacement is `o(1)`
in normalized Hilbert--Schmidt norm. Condition `(IR2)` makes the resulting
ultraproduct homomorphism kill `K` and hence factor through `Q=F/K`. By the
orthogonal splitting

```text
||(Pi_n(f)-1)P_n||_2^2
 = ||(A_n(f)-1)P_n||_2^2 + ||(1-P_n)Pi_n(f)P_n||_2^2,
```

`(IR1)` and `(IR3)` make that quotient homomorphism nontrivial. Since
`Q=EL_4(L_(F_2)(1,2))` is simple, its kernel is trivial.

An injective homomorphism into a tracial matrix ultraproduct is the standard
abstract-unitary formulation of hyperlinearity. Explicitly, Cesaro direct
sums of tensor powers suppress every nonidentity scalar phase as well as every
trace of modulus less than one; diagonalizing over finite subsets gives the
canonical trace models in `hyperlinear-elementwise-visibility`. Thus `Q` is
hyperlinear. The established `GL=EL` identification transfers this to the
binary Leavitt unit-group target.

The established nonsoficity of `Q` then makes it the requested hyperlinear
nonsofic group. This route uses no claim that weak/operator-MF selects a trace:
all trace visibility is concentrated in the open retention condition `(IR)`.
