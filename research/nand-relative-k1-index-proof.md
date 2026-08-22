---
rg: 2
id: nand-relative-k1-index-proof
kind: route
title: Compute the relative six-term sequence and the finite Weyl realization
target: nand-triangle-relative-k1-is-a-finite-packet-index
requires:
  - s4-nand-cycle-holonomy-is-one-s2-bit
  - odd-nand-phase-return-has-exact-finite-models
---

Order the atom basis as `(+,+),(+,-),(-,+)`.  Then `D` is the diagonal
algebra and the spectral multiplicities of the shared separator give
`B=M_2(C) directSum C`.  Algebraic `K_1` of a finite product is the product
of its `K_1` groups, and determinant gives

```text
K_1(M_2(C))=C^x,       K_1(C)=C^x.
```

The inclusion of `D` into `B` sends its first two scalar units to a diagonal
matrix in the `M_2` block, proving `(NKT2)` and surjectivity.  On `K_0`, both
first two minimal projections become the minimal generator of the `M_2`
block, while the third becomes the generator of the scalar block.  The
six-term sequence therefore gives `(NKT4)--(NKT5)`.  Direct determinants of
the transposition matrix and of `-I_3` give `(NKT6)--(NKT7)`.  The relative
class is represented by the projection-transition triple
`(e_(+,+),e_(+,-),H)`, whose boundary is the oriented difference of the
exchanged atom classes; the absolute class of `H` comes from `K_1(D)` and
vanishes relatively.  The central phase already lies in `D` and has zero
boundary.

For the normalizer computation, a unitary in `B` normalizing the three
minimal diagonal projections can phase each line and may permute the two
equal separator-plus lines; it cannot exchange either with the separator-
minus line.  Modulo `U(D)` the quotient is therefore `S_2`, acting on
`K_0(D)` by the stated transposition.  Finally the exact model `(NKT9)` is
the signed-permutation triangle already proved by
`odd-nand-phase-return-has-exact-finite-models`.
