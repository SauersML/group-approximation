---
rg: 2
id: fixed-holonomy-on-overlap-pays-relator-energy-proof
kind: route
title: Compress to the corner and minimize the multiplicity trace
target: fixed-holonomy-on-overlap-pays-relator-energy
requires: []
---

**`(FHO1)`.**  Compressing to `R` cannot increase the Hilbert--Schmidt norm:

```text
||W - 1||_2^2 >= ||(W-1)R||_2^2 = tau( R (W-1)^* (W-1) R ).
```

On the corner, `(W-1)^*(W-1) = 2 - W - W^*`, so the right side equals
`tau(R)` times the normalized corner value of `2 - 2 Re tr(W|_R)`.  Substituting
the factorization and using multiplicativity of the normalized trace across a
tensor product,

```text
tr(W|_R) = tr(A) tr(H),
```

hence

```text
||W - 1||_2^2 >= tau(R) ( 2 - 2 Re( tr(A) tr(H) ) ).
```

Finally `|tr H| <= 1` because `H` is a contraction and the trace is normalized,
so `Re(tr(A)tr(H)) <= |tr A|` and

```text
||W - 1||_2^2 >= 2 (1 - |tr A|) tau(R),
```

which is `(FHO1)`.  The estimate is uniform over `H`, which is the assertion
that multiplicity cannot dilute it.

**`(FHO2)`.**  With `X|_R = U tensor H_1` and `Y|_R = V tensor H_2`,

```text
[X,Y]|_R = XYX^(-1)Y^(-1)|_R
         = (UVU^(-1)V^(-1)) tensor (H_1H_2H_1^(-1)H_2^(-1))
         = [U,V] tensor 1,
```

using that `H_1` and `H_2` commute; more generally the multiplicity factor is
some contraction `H`, and applying `(FHO1)` with `A = [U,V]` gives `(FHO2)`.

**`(FHO3)`.**  Let `U,V` be distinct reflections in the standard two-dimensional
representation of `S_3`.  Both are involutions, so

```text
[U,V] = U V U^(-1) V^(-1) = (UV)^2,
```

and `UV` is a rotation of order three.  Hence `(UV)^2` is rotation by `240`
degrees, with ordinary trace `2 cos(240 deg) = -1` and normalized trace `-1/2`.
Then `2(1 - |-1/2|) = 1`, giving `(FHO3)`.

**`(FHO4)`.**  Sum `(FHO3)` over the pairs of an incompatibility graph and apply
`(IGS3)` of `incompatibility-graph-spectrum-forces-overlap` to the total
overlap.
