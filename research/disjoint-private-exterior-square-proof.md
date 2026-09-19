---
rg: 2
id: disjoint-private-exterior-square-proof
kind: route
title: Union-bound alternating forms over independent disjoint label pairs
target: disjoint-private-pairs-expand-the-full-exterior-square
requires: []
---

Choose all `2M` labels independently and uniformly.  A nonzero alternating
form `beta` has rank at least two.  For independent uniform `v,w`,

```text
Pr[beta(v,w)=1]=(1-2^(-rank beta))/2 >=3/8.               (DPE2)
```

The `M` disjoint pairs are independent.  Hoeffding therefore gives, for one
fixed nonzero `beta`,

```text
Pr[(1/M)sum_t beta(v_(2t-1),v_(2t))<1/4] <=exp(-M/32).
```

There are fewer than `2^(r(r-1)/2)` alternating forms.  Taking
`M>16(log 2)r(r-1)` makes the union bound strictly smaller than one and proves
existence of `(DPE1)`.

If a central class-two representation passes every paired jointness view,
its alternating commutator form vanishes on every sampled wedge.  Their span
is all of `Lambda^2(F_2^r)` by `(DPE1)`, so the form is zero.  The same finite
sample property can be included in recursive lexicographic selection.
