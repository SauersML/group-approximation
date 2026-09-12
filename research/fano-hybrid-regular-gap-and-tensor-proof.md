---
rg: 2
id: fano-hybrid-regular-gap-and-tensor-proof
kind: route
title: Compare group-basis support, then odd-tensor three honest scalar sectors
target: fano-hybrid-reflection-has-a-universal-regular-hs-gap
requires:
  - universal-central-selector-word-is-affine-for-any-actor
  - tensor-affine-selector-pattern-barrier
---

First suppose `w notin D`. The group-basis support of

```text
e_-w=(w-Jw)/2
```

is disjoint from `D`, whereas `R in C[D]`. Both vectors have squared
`L^2`-norm `tau(e_-)=1/2`, so orthogonality gives

```text
||e_-w-R||_2^2=1.                                     (FHR1)
```

Now suppose `w in D`. On the four marked characters of `D`, the value of
`w` is an affine Boolean phase in `(P,F)`. The phase of `R` is negative at
one point and positive at three. Every affine phase differs from this table
at at least one point, and the constant positive phase differs at exactly
one. Each marked atom has canonical trace `1/8`; a sign disagreement
contributes `4/8=1/2` to the squared norm. This proves `(FHG2)` and sharpness.
Dividing by `tau(e_-)=1/2` gives `(FHG3)`.

For the finite-dimensional assertion, tensor the three representations in
`(FHG4)`. Scalar projection bits add modulo two under multiplication of their
signs, so

```text
(0,0,0)+(1,0,0)+(1,1,0)=(0,1,0) in F_2^3,            (FHR2)
```

where the third bit records whether `r=-1`. The tensor has marked phase
`(-1)^3=-1`, input `(P,F)=(0,1)`, and output `r=+1`. Thus it is the wrong
sector `(FHG5)` while satisfying every group relator exactly.
---
