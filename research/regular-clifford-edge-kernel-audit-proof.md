---
rg: 2
id: regular-clifford-edge-kernel-audit-proof
kind: route
title: Check the class-two normal forms and induce the component map over the regular orbit
target: regular-clifford-edge-map-has-zero-kernel
requires:
  - affine-selector-clifford-residual-packet
  - affine-selector-clifford-rank-swap-balanced
  - s3-reset-plane-has-common-invariant-selector-polarization
  - regular-orbit-induction-coherifies-finite-edges
---

The affine packet supplies the five Schur commutator matrices on the
thirty-dimensional residual quotient.  Add the dummy alternating block on
the source and the two complementary blocks of `(GRS3)` on the fresh side.
Under `(RCK3)`, the two fresh commutators add to

```text
s+(J+s)=J,
```

so every source commutator form is the pullback of its fresh form.  Images of
the two dummy involutions remain involutions because the two sign-controlled
pairs commute.  This proves that `(RCK3)` is a homomorphism.

Every element has a class-two normal form consisting of one center vector and
one quotient vector.  The exact binary quotient matrix for `(RCK3)` has rank
`32`, and its center matrix has rank `5`.  A kernel element therefore first
has zero quotient vector and then zero center vector.  This proves the
component injection without appealing to representation dimensions.

For the residual one-copy obstruction, congruence of a pair of invertible
alternating forms preserves the similarity class of their transition
operator.  The polynomial nullities in `(RCK7)` are similarity invariants and
separately obstruct the swap and shear generators.  They allow all of
`GL_30(F_2)`, so in particular they obstruct any residual Clifford action.

Finally take the sixfold central product.  The component injection is block
diagonal and the regular `S_3` acts by the same factor permutations on source
and target.  The replay checks equivariance on a basis; injectivity of the
semidirect extension then follows from injectivity on the base and identity
on `S_3`.  Identifying the residual factors replaces six independent copies
of `F_2^30` by their diagonal quotient, whose kernel dimension is
`6*30-30=150`.  This proves both the positive private-factor statement and
its precise sharing boundary.
