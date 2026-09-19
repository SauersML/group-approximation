---
rg: 2
id: atlas-a8-four-cycle-controls-raw-s3-energy-proof
kind: route
title: Telescope the eight-letter t21 word and apply weighted Cauchy
target: atlas-a8-four-cycle-controls-raw-s3-energy
requires: []
artifacts:
  - experiments/atlas_a8_four_cycle_raw_s3.py
  - experiments/atlas-raw-reynolds-gap-audit.json
---

The exact raw-word audit identifies

```text
h_a=t21,
h_b=t12.
```

The four-cycle audit verifies the identity

```text
t21 = t01 t30 t23 t30 t01 t30 t23 t30.               (1)
```

For

```text
d(g)=||[U,lambda_k(g)]||_2,
```

the commutator identity

```text
[U,lambda(xy)]
 =[U,lambda(x)]lambda(y)+lambda(x)[U,lambda(y)]
```

and unitary invariance give the subadditivity

```text
d(xy)<=d(x)+d(y).                                      (2)
```

Apply `(2)` along `(1)`.  Writing `d_ij=d(tij)`,

```text
d(t21) <= 2 d_01 + 2 d_23 + 4 d_30.
```

Cauchy--Schwarz with coefficient vector `(2,2,4)` gives

```text
d(t21)^2
 <= (2^2+2^2+4^2)(d_01^2+d_23^2+d_30^2)
 =24(d_01^2+d_23^2+d_30^2).                           (3)
```

Since `h_b=t12`, its contribution is exactly `d_12^2`.  Adding it to `(3)`
and using `1<=24` yields

```text
d(h_a)^2+d(h_b)^2
 <=24(d_01^2+d_12^2+d_23^2+d_30^2),
```

which is `(A8-RAW-24)`.  No averaging over A8 and no full Cayley-diameter
estimate is used.
