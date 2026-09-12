---
rg: 2
id: atlas-three-word-c6-s3-core
kind: claim
title: The three-word atlas test is exactly a C6-versus-S3 regular-representation problem
artifacts:
  - experiments/atlas_three_word_permutation_countermodel.py
  - experiments/atlas-word-19243.json
distinct_from:
  atlas-a4-three-word-amplified-gap: that asks for a positive lower bound on the resulting three defects; this claim only removes the irrelevant ambient A8 coordinates and rewrites the exact finite support.
---

Let `u,v` be packet indices `6910,6940` and `q=q_19243`.  The three-word
energy depends only on order-six subgroups of the two regular `A8` charts.
More precisely, after regular subgroup frames it is the following universal
finite problem.

On `C^(6m)` let `r,c` be `m Reg(C6)`, with

```text
r^3=c^2=1,   [r,c]=1,
```

and let `x,y` be `m Reg(S3)`, with `x^3=y^2=1` and `y x y=x^-1`.  Put
`z=yx`, another involution.  For an arbitrary relative unitary between the two
regular subgroup representations the three atlas words are exactly

```text
u = (y r)^3,
v = (z r^-1)^3,
q = x c y c x^-1 c z c.                              (C6-S3-CORE)
```

The infimum of the normalized-HS sum of the three squared defects in the
original `Reg(A8) tensor I_k` problem is **equal** to the infimum of
`(C6-S3-CORE)` over all integers `m>=1`.

Indeed both order-six restrictions of `Reg(A8)` are `3360 Reg(order-six
subgroup)`.  Thus the original problem is the subfamily `m=3360 k`.  Conversely
any `m`-dimensional-multiplicity core can be amplified by `3360` without
changing normalized defects, landing in the original family with `k=m`.

So amplification is not an A8 representation-theory issue at all: the entire
three-word candidate lives on a six-state finite alphabet on each side.
