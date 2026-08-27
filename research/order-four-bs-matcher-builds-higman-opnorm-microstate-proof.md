---
rg: 2
id: order-four-bs-matcher-builds-higman-opnorm-microstate-proof
kind: route
title: Conjugate one approximate BS row four times and pay the cyclic return
target: order-four-bs-matcher-builds-higman-opnorm-microstate
requires: []
---

Put `X_i=K^i P K^(-i)` for every integer `i`, and put `X=KPK^*`.  The exact
Baumslag--Solitar relation and `(HOM1)` give

```text
||P X P^* - X^2||
 <= ||P(X-D)P^*||+||D^2-X^2||
 <= epsilon+2epsilon=3epsilon.                        (1)
```

Conjugating `(1)` by `K^i` yields

```text
||X_i X_(i+1) X_i^* - X_(i+1)^2||<=3epsilon          (2)
```

for every integer `i`.  For `i=0,1,2`, `(2)` is exactly the corresponding
cyclic Higman row of `(HOM2)`.

For the last row, compare its repeated occurrence `X_0` with the noncyclic
next occurrence `X_4`.  Since

```text
||X_4-X_0||=||K^4 P K^(-4)-P||=r,
```

unitary invariance and `||A^2-B^2||<=2||A-B||` give

```text
||X_3X_0X_3^*-X_0^2||
 <= ||X_3X_4X_3^*-X_4^2||+r+2r
 <=3epsilon+3r.                                       (3)
```

This proves `(HOM3)`.  Equation `(HOM4)` is unitary conjugacy.  For the
periodic clock, `P_n` has `-1` as an eigenvalue, so `||P_n-1||=2`; applying
`(HOM3)--(HOM4)` proves the final assertion.
