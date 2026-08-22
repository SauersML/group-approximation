---
rg: 2
id: private-random-affine-rank-condenser-proof
kind: route
title: Union-bound random rank-one measurements against all low-rank forms
target: private-random-generator-columns-form-affine-rank-condenser
requires: []
---

It suffices to work in the active `r`-space.  Fix a matrix `Q` of rank at
most `r/4` and put `M=I_r+Q`.  Rank subadditivity gives

```text
rank(M)>=3r/4.                                               (1)
```

For independent uniform `a,b in F_2^r`,

```text
Pr[a^T M b=1]=(1-2^(-rank(M)))/2.                            (2)
```

Indeed `M b` is nonzero with probability `1-2^(-rank(M))`, and conditional
on this event its dot product with uniform `a` is balanced.  For large `r`,
the probability in `(2)` is at least `7/16`.  Hoeffding therefore gives

```text
Pr[ (1/m) sum_t 1_(a_t^T M b_t=1) < 1/4 ]
 <= exp(-m/32).                                              (3)
```

The number of `r`-square matrices of rank at most `r/4` is at most

```text
(r/4+1) 2^(r^2/2),                                          (4)
```

because every rank-`k` matrix factors as an `r by k` matrix times a `k by r`
matrix.  With `m=64r^2`, the union of the bad events in `(3)` over `(4)` has
probability less than one for all sufficiently large `r`.  Hence one sample
family satisfies `(PRC1)` simultaneously for every such `Q`.

Embed the active block in `F_2^N`.  The restriction of any ambient matrix of
rank at most `r/4` to that block also has rank at most `r/4`, so the same
estimate applies.  If the original good generator block has length `cN` and
relative distance `delta`, after appending `64r^2<=64N` columns every nonzero
functional still has relative weight at least

```text
delta c/(c+64)>0.
```

Thus both column measures retain uniform spectral constants and total length
`Theta(N)`.  Finally an exact scalar Weyl form of rank `s` has minimum carrier
dimension `2^s`; `(PRC1)` proves `(PRC2)`.
