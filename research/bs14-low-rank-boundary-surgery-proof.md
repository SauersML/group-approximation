---
rg: 2
id: bs14-low-rank-boundary-surgery-proof
kind: route
title: Polarize the compressed involution and count boundary excursions
target: bs14-low-rank-boundary-surgery-preserves-the-regular-face
requires:
  - bs14-trivial-boundary-inversion-forces-r-fixed-source
  - bs14-regular-character-forces-sublinear-fixed-source
---

The involution block equations `(TBI3)` give `1-A^2=BB*`.  Functional
calculus on the selfadjoint contraction `A` yields

```text
(sgn(a)-a)^2<=(1-a^2)
```

and proves `(LRS3)`.  The kernel and polar-intertwining arguments in the
claim prove `(LRS2)`.

Insert `P+Q=1` between the three factors of `Y~_i^3`.  The all-`P` term is
`(AU_i)^3`; each other term factors through `Q`, and there are three such
compressed path patterns.  Telescope the three occurrences of `A` to
`X_0`.  This proves the rank and Frobenius estimates `(LRS4)` after enlarging
one universal constant.

Word telescoping shows that a generator perturbation supported on at most
`r` dimensions changes a word of fixed length `ell` by at most
`O(ell sqrt(r/d))` in normalized HS norm.  The normalized trace difference
is bounded by the same norm, proving preservation of the regular character.

