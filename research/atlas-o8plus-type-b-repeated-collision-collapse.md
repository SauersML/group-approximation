---
rg: 2
id: atlas-o8plus-type-b-repeated-collision-collapse
kind: claim
title: The high-centralizer natural Omega8+(2) Q1920 twist collapses at every multiplicity
distinct_from:
  atlas-o8plus-type-a-repeated-collision-collapse: that treats the other orthogonal embedding twist, whose A-centralizer has dimension 12; this treats the dimension-20 twist.
  atlas-o8plus-type-b-multiplicity-two-collision-collapse: that exhausts only H^2 by Boolean SAT; this is an arbitrary-multiplicity theorem over a free associative coefficient algebra.
  atlas-q1920-psl5-double-natural-module-has-no-collision-seam: that treats a five-dimensional module factoring through Q/Z(Q); this treats a faithful indecomposable eight-dimensional Q-module.
---

Let `H` be the natural eight-dimensional `F2` module restricted from the
canonical singular-parabolic copy of `Q=2^5:A5` in `Omega8+(2)`.  For either
marked Q tuple, choose the embedding twist with

```text
H|_A = 1^4 + U^2,      dim_F2 End_A(H)=20,      A=<r,u>~=S3,
```

where `U` is the absolutely irreducible two-dimensional `F2[S3]`-module.
For every `m>=1`, let Q act diagonally on `H^m`.  If an A-central operator `c`
satisfies

```text
c^2=1,
(c t)^3=1,
t c s c t^-1 c s t c=1,
```

then `c=1`.  Hence the protected collision subgroup `<t,s,c>~=S4` cannot
occur in any repeated copy of either Type-B marked twist inside
`GL_(8m)(2)=PSL_(8m)(2)`.

Together with `atlas-o8plus-type-a-repeated-collision-collapse`, this excludes
both embedding twists of the natural `Omega8+(2)` module at every
multiplicity.  It does not classify unrelated `F2[Q]`-modules or mixed
isotypic sums.
