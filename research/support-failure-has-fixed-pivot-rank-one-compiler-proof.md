---
rg: 2
id: support-failure-has-fixed-pivot-rank-one-compiler-proof
kind: route
title: Use the fixed pivot and the determinant (one plus e) times f
target: support-failure-has-fixed-pivot-rank-one-compiler
requires: []
artifacts:
  - experiments/minimal_rank_one_support_compiler.py
---

The first entry of `M_sub(e,f)` is one, so the rank is always at least one.
Its determinant over `F_2` is

```text
det M_sub(e,f) = f(1+e).
```

The matrix therefore has rank two exactly at `(e,f)=(0,1)` and rank one at
the other three assignments.  This proves `(SFP2)` and the fixed-pivot claim.

For the finite exhaustive statement, each affine form in two variables is one
of eight coefficient triples.  The verifier loops over all four-entry tuples,
evaluates the four binary ranks by the determinant test above, and sorts the
survivors by `(number of nonzero entries, total number of affine monomials)`.
The committed output counts are reproduced in the synthesis artifact.
