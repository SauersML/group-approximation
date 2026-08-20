---
rg: 2
id: fanizza-rank-gates-have-a-one-bit-character-escape-proof
kind: route
title: Read the selector derivative as one outer product
target: fanizza-rank-gates-have-a-one-bit-character-escape
requires:
  - fanizza-fixed-nonlinear-menu-has-small-rank-gates
artifacts:
  - experiments/fanizza_fixed_predicate_rank_compiler.py
---

For an affine matrix, toggling only bit `i` cancels the constant term and all
other coefficients, leaving `A_i`.  The script extracts every coefficient
matrix from the three verified optimized gates and computes the exact ranks
in `(OBE2)` by Gaussian elimination over `F_2`.

If `A_i=u v^T` has rank one, the associated alternating Clifford form is

```text
[[0,A_i],[A_i^T,0]],
```

which has rank two.  Replacing p- and q-coordinates by constant invertible row
and column changes sends `u,v` to basis vectors, so the difference is one
standard anticommuting pair.  Those changes are products of commuting packet
generators and therefore give literal group words.
