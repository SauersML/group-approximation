---
rg: 2
id: parity-headed-compressor-kills-mark-in-exact-matrix-models
kind: claim
title: A parity-headed one-sided compressor kills its central mark in every exact matrix model
distinct_from:
  schur-predicate-is-character-density-difference: that converts arbitrary Boolean predicates into character-density gaps; this uses one parity character to isolate the smallest possible two-point return obstruction.
---

Let `Lambda` be a group, let `alpha:Lambda->Lambda` be injective, and let
`chi:Lambda->C_2` be a nonzero character such that

```text
chi alpha=0.                                                   (PHC1)
```

Adjoin a central involution `J`, an involution `q`, and a stable letter `t`,
with

```text
q g q^(-1)=J^(chi(g)) g,       g in Lambda,
t g t^(-1)=alpha(g),            g in Lambda.                  (PHC2)
```

Call the resulting HNN extension `H(alpha,chi)`. Then:

1. the base group embeds in `H(alpha,chi)`, so `J!=1`;
2. every finite-dimensional unitary representation `rho` of
   `H(alpha,chi)` satisfies `rho(J)=1`.

Consequently `J` is invisible in every exact finite-dimensional model even
though it is a genuine group element. This does **not** prove that `H` is
nonhyperlinear: a normalized-Hilbert--Schmidt microstate need not be close to
an exact representation.
