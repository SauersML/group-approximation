---
rg: 2
id: two-by-two-support-compiler-has-unique-fixed-pivot-proof
kind: route
title: Normalize one pivot and rule out the eight possible second pivots by affine support size
target: two-by-two-support-compiler-has-unique-fixed-pivot
requires: []
artifacts:
  - experiments/minimal_rank_one_support_compiler.py
---

Suppose a pivot exists.  Constant row and column changes in `GL_2(F_2)` move
it to `(e_1,e_1)`, so write

```text
M=[[1,a],[b,d]]
```

with `a,b,d` affine.  The fixed pivot makes the rank profile equivalent to

```text
d+ab=(1+e)f.                                           (1)
```

A second nonzero row/column pair is one of the eight remaining pairs in
`{e_1,e_2,e_1+e_2}^2`.  Requiring its pairing to be the constant one gives,
respectively, one of

```text
a=1, b=1, d=1, a=0, b=0, b+d=1, a+d=1, d=a+b.        (2)
```

If `a` or `b` is zero or one, the left side of `(1)` is affine, whereas
`(1+e)f` is not.  If `d=1`, equation `(1)` says `ab=1+(1+e)f`; the right side
has support size three, while the product of two affine Boolean forms has
support size `0,1,2`, or `4`.  The cases `b+d=1` and `a+d=1` give the same
support-size contradiction after rewriting as `b(1+a)=1+(1+e)f` or its
transpose.  Finally `d=a+b` makes `d+ab=a OR b`; a union of supports of affine
forms cannot be the singleton support of `(1+e)f`.  Every case in `(2)` is
impossible, proving uniqueness.
