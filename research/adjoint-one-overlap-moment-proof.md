---
rg: 2
id: adjoint-one-overlap-moment-proof
kind: route
title: Compress the returned Reynolds range and expand the adjoint trace
target: adjoint-reynolds-return-needs-one-overlap-moment
requires:
  - predicate-rank-jump-forces-adjoint-reynolds-gap
---

Positivity and cyclicity give

```text
Theta=tr_ad(R_B T R_A T^*)<=tr_ad(R_B),
```

which is `(SOM2)`.  Since `R_A,R_B` are orthogonal projections and `T` is
unitary,

```text
||(I-R_B)TR_A||_(HS,ad)^2
 =tr_ad(R_A T^*(I-R_B)T R_A)
 =tr_ad(R_A)-Theta,
```

proving `(SOM3)`.  Combine `(SOM2)` and `(SOM4)` with the Reynolds rank gap
`(ARG1)` to get `(SOM5)`.

Finally expand all three Reynolds averages in `(SOM1)`.  Composition of
adjoint operators multiplies their implementing unitaries, and

```text
tr_ad(Ad_V)=|tr_d(V)|^2.
```

This proves `(SOM7)` (with inverses moved between the dummy variables if the
opposite averaging convention is used).
