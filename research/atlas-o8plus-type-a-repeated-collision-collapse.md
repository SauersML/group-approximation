---
rg: 2
id: atlas-o8plus-type-a-repeated-collision-collapse
kind: claim
title: The low-centralizer natural Omega8+(2) Q1920 twist collapses at every multiplicity
distinct_from:
  atlas-o8plus-canonical-moved-module-completion-fails: that exhausts one copy inside the orthogonal group; this allows arbitrary GL block mixing across every multiplicity, but only for the dimension-12 centralizer twist.
  atlas-gl6-repeated-affine-collision-collapse: that treats the faithful six-dimensional homogeneous-affine modules; this treats an indecomposable eight-dimensional orthogonal-natural module with composition factors 1,1,4,1,1.
  atlas-psl5-repeated-natural-collision-collapse: that treats five-dimensional modules factoring through Q/Z(Q); this eight-dimensional module is faithful on Q.
---

Let `H` be the natural eight-dimensional `F2` module restricted from the
canonical singular-parabolic copy of `Q=2^5:A5` in `Omega8+(2)`.  For either
marked Q tuple, choose the ambient embedding twist for which

```text
dim_F2 End_A(H)=12,             A=<r,u>~=S3.             (O8A-1)
```

For every `m>=1`, let Q act diagonally on `H^m`.  If an operator `c`
centralizes A and satisfies

```text
c^2=1,
(c t)^3=1,
t c s c t^-1 c s t c=1,                              (O8A-2)
```

then `c=1`.  Thus the protected collision subgroup `<t,s,c>~=S4` cannot
occur in any repeated copy of this twist inside
`GL_(8m)(2)=PSL_(8m)(2)`.

This is an exact infinite-family exclusion, not a bounded matrix census.
The other ambient twist has `dim End_A(H)=20`; it is explicitly outside the
claim and remains the next coefficient-algebra case.
